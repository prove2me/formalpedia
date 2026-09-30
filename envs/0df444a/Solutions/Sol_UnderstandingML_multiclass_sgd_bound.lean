-- Prove2me | solution 1 for UnderstandingML.multiclass_sgd_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T06:40:55.878334+00:00
-- url     : https://prove2.me/submissions/73e259b7-ed9c-46d6-b1fe-820a3f4ec1df

import Definitions.Def_UnderstandingML_Multiclass
import Theorems.Thm_UnderstandingML_sgd_learns_convex_lipschitz

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

namespace MulticlassSGDAux

variable {d : ℕ} {X Y : Type*} [Fintype Y] [Nonempty Y]

/-- `Classical.choose` only depends on the predicate. -/
theorem choose_congr {α : Sort*} {P Q : α → Prop} (hPQ : P = Q) (hp : ∃ x, P x)
    (hq : ∃ x, Q x) : Classical.choose hp = Classical.choose hq := by
  subst hPQ; rfl

/-- The terms of the maximum in (17.3). -/
noncomputable def term (Δ : Y → Y → ℝ) (Ψ : X → Y → Vec d) (w : Vec d) (z : X × Y) (y' : Y) :
    ℝ :=
  Δ y' z.2 + ⟪w, Ψ z.1 y' - Ψ z.1 z.2⟫_ℝ

omit [Nonempty Y] in
theorem term_le (Δ : Y → Y → ℝ) (Ψ : X → Y → Vec d) (w : Vec d) (z : X × Y) (y' : Y) :
    term Δ Ψ w z y' ≤ genHingeLoss Δ Ψ w z :=
  le_ciSup (Finite.bddAbove_range (fun y' ↦ term Δ Ψ w z y')) y'

omit [Fintype Y] in
theorem genHinge_le (Δ : Y → Y → ℝ) (Ψ : X → Y → Vec d) (w : Vec d) (z : X × Y) (c : ℝ)
    (hc : ∀ y', term Δ Ψ w z y' ≤ c) : genHingeLoss Δ Ψ w z ≤ c :=
  ciSup_le hc

theorem argmax_spec (Δ : Y → Y → ℝ) (Ψ : X → Y → Vec d) (w : Vec d) (z : X × Y) (y' : Y) :
    term Δ Ψ w z y' ≤ term Δ Ψ w z (genHingeArgmax Δ Ψ w z) := by
  have := (Classical.choose_spec (Finset.exists_max_image Finset.univ
    (fun y' ↦ Δ y' z.2 + ⟪w, Ψ z.1 y' - Ψ z.1 z.2⟫_ℝ) Finset.univ_nonempty)).2 y'
    (Finset.mem_univ _)
  exact this

theorem genHinge_eq_argmax (Δ : Y → Y → ℝ) (Ψ : X → Y → Vec d) (w : Vec d) (z : X × Y) :
    genHingeLoss Δ Ψ w z = term Δ Ψ w z (genHingeArgmax Δ Ψ w z) :=
  le_antisymm (genHinge_le _ _ _ _ _ (argmax_spec Δ Ψ w z)) (term_le _ _ _ _ _)

/-- The direction `Ψ(x, ŷ) − Ψ(x, y)` is a subgradient of the generalized hinge loss. -/
theorem isLossSubgradientSelector (Δ : Y → Y → ℝ) (Ψ : X → Y → Vec d) :
    IsLossSubgradientSelector (genHingeLoss Δ Ψ) (genHingeDirection Δ Ψ) := by
  intro w z u
  show genHingeLoss Δ Ψ w z + ⟪u - w, genHingeDirection Δ Ψ w z⟫_ℝ ≤ genHingeLoss Δ Ψ u z
  rw [genHinge_eq_argmax Δ Ψ w z]
  refine le_trans ?_ (term_le Δ Ψ u z (genHingeArgmax Δ Ψ w z))
  simp only [term, genHingeDirection]
  rw [inner_sub_left]
  linarith

theorem convexOn (Δ : Y → Y → ℝ) (Ψ : X → Y → Vec d) (z : X × Y) :
    ConvexOn ℝ Set.univ (fun w ↦ genHingeLoss Δ Ψ w z) := by
  refine ⟨convex_univ, fun u _ v _ a b ha hb hab ↦ ?_⟩
  apply genHinge_le
  intro y'
  have hu := term_le Δ Ψ u z y'
  have hv := term_le Δ Ψ v z y'
  have e : term Δ Ψ (a • u + b • v) z y' = a * term Δ Ψ u z y' + b * term Δ Ψ v z y' := by
    simp only [term]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have : Δ y' z.2 = (a + b) * Δ y' z.2 := by rw [hab, one_mul]
    linarith [this]
  rw [e, smul_eq_mul, smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hu ha) (mul_le_mul_of_nonneg_left hv hb)

theorem lipschitz (Δ : Y → Y → ℝ) (Ψ : X → Y → Vec d) {ρ : ℝ}
    (hbound : ∀ x y, ‖Ψ x y‖ ≤ ρ / 2) (z : X × Y) (u v : Vec d) :
    genHingeLoss Δ Ψ u z ≤ genHingeLoss Δ Ψ v z + ρ * ‖u - v‖ := by
  apply genHinge_le
  intro y'
  have h1 := term_le Δ Ψ v z y'
  have hn : ‖Ψ z.1 y' - Ψ z.1 z.2‖ ≤ ρ := by
    calc ‖Ψ z.1 y' - Ψ z.1 z.2‖ ≤ ‖Ψ z.1 y'‖ + ‖Ψ z.1 z.2‖ := norm_sub_le _ _
      _ ≤ ρ / 2 + ρ / 2 := add_le_add (hbound _ _) (hbound _ _)
      _ = ρ := by ring
  have h2 : ⟪u - v, Ψ z.1 y' - Ψ z.1 z.2⟫_ℝ ≤ ρ * ‖u - v‖ := by
    calc ⟪u - v, Ψ z.1 y' - Ψ z.1 z.2⟫_ℝ ≤ ‖u - v‖ * ‖Ψ z.1 y' - Ψ z.1 z.2‖ :=
          real_inner_le_norm _ _
      _ ≤ ‖u - v‖ * ρ := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      _ = ρ * ‖u - v‖ := mul_comm _ _
  have e : term Δ Ψ u z y' = term Δ Ψ v z y' + ⟪u - v, Ψ z.1 y' - Ψ z.1 z.2⟫_ℝ := by
    simp only [term]; rw [inner_sub_left]; ring
  linarith

theorem isLipschitzLoss (Δ : Y → Y → ℝ) (Ψ : X → Y → Vec d) {ρ : ℝ}
    (hbound : ∀ x y, ‖Ψ x y‖ ≤ ρ / 2) : IsLipschitzLoss ρ (genHingeLoss Δ Ψ) := by
  intro z w₁ w₂
  rw [abs_sub_le_iff]
  constructor
  · linarith [lipschitz Δ Ψ hbound z w₁ w₂]
  · have := lipschitz Δ Ψ hbound z w₂ w₁
    rw [norm_sub_rev] at this
    linarith

omit [Nonempty Y] in
theorem nonneg (Δ : Y → Y → ℝ) (hΔ0 : ∀ y, Δ y y = 0) (Ψ : X → Y → Vec d) (w : Vec d)
    (z : X × Y) : 0 ≤ genHingeLoss Δ Ψ w z := by
  have := term_le Δ Ψ w z z.2
  simpa [term, hΔ0] using this

theorem le_at_zero (Δ : Y → Y → ℝ) (Ψ : X → Y → Vec d) (z : X × Y) :
    genHingeLoss Δ Ψ 0 z ≤ ⨆ p : Y × Y, Δ p.1 p.2 := by
  apply genHinge_le
  intro y'
  simp only [term, inner_zero_left, add_zero]
  exact le_ciSup (Finite.bddAbove_range (fun p : Y × Y ↦ Δ p.1 p.2)) (y', z.2)

section Measurability

variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSingletonClass Y]

omit [Nonempty Y] in
theorem measurable_psi (Ψ : X → Y → Vec d) (hΨ : ∀ y, Measurable (fun x ↦ Ψ x y)) :
    Measurable (fun p : X × Y ↦ Ψ p.1 p.2) :=
  measurable_from_prod_countable_left (fun y ↦ hΨ y)

omit [Nonempty Y] in
theorem measurable_term (Δ : Y → Y → ℝ) (Ψ : X → Y → Vec d)
    (hΨ : ∀ y, Measurable (fun x ↦ Ψ x y)) (y' : Y) :
    Measurable (fun p : Vec d × (X × Y) ↦ term Δ Ψ p.1 p.2 y') := by
  have h1 : Measurable (fun p : Vec d × (X × Y) ↦ Δ y' p.2.2) :=
    (measurable_of_countable (Δ y')).comp (measurable_snd.comp measurable_snd)
  have h2 : Measurable (fun p : Vec d × (X × Y) ↦ Ψ p.2.1 y') :=
    (hΨ y').comp (measurable_fst.comp measurable_snd)
  have h3 : Measurable (fun p : Vec d × (X × Y) ↦ Ψ p.2.1 p.2.2) :=
    (measurable_psi Ψ hΨ).comp measurable_snd
  exact h1.add (continuous_inner.measurable.comp (measurable_fst.prodMk (h2.sub h3)))

omit [Nonempty Y] in
theorem measurable_genHinge (Δ : Y → Y → ℝ) (Ψ : X → Y → Vec d)
    (hΨ : ∀ y, Measurable (fun x ↦ Ψ x y)) :
    Measurable (Function.uncurry (genHingeLoss Δ Ψ)) := by
  have : Function.uncurry (genHingeLoss Δ Ψ) =
      fun p : Vec d × (X × Y) ↦ ⨆ y', term Δ Ψ p.1 p.2 y' := rfl
  rw [this]
  exact Measurable.iSup (fun y' ↦ measurable_term Δ Ψ hΨ y')

/-- The canonical maximizer is a function of the set of maximizers. -/
theorem measurable_argmax (Δ : Y → Y → ℝ) (Ψ : X → Y → Vec d)
    (hΨ : ∀ y, Measurable (fun x ↦ Ψ x y)) :
    Measurable (fun p : Vec d × (X × Y) ↦ genHingeArgmax Δ Ψ p.1 p.2) := by
  classical
  let S : Y → Set (Vec d × (X × Y)) := fun y₀ ↦
    {p | ∀ y', term Δ Ψ p.1 p.2 y' ≤ term Δ Ψ p.1 p.2 y₀}
  have hS : ∀ y₀, MeasurableSet (S y₀) := fun y₀ ↦ by
    have : S y₀ = ⋂ y', {p | term Δ Ψ p.1 p.2 y' ≤ term Δ Ψ p.1 p.2 y₀} := by
      ext p; simp [S]
    rw [this]
    exact MeasurableSet.iInter fun y' ↦
      measurableSet_le (measurable_term Δ Ψ hΨ y') (measurable_term Δ Ψ hΨ y₀)
  let Φ : Vec d × (X × Y) → (Y → Bool) := fun p y₀ ↦ decide (p ∈ S y₀)
  have hΦ : Measurable Φ := by
    rw [measurable_pi_iff]
    intro y₀
    refine measurable_to_countable' fun b ↦ ?_
    cases b
    · have : (fun p ↦ Φ p y₀) ⁻¹' {false} = (S y₀)ᶜ := by ext p; simp [Φ]
      rw [this]; exact (hS y₀).compl
    · have : (fun p ↦ Φ p y₀) ⁻¹' {true} = S y₀ := by ext p; simp [Φ]
      rw [this]; exact hS y₀
  let sel : (Y → Bool) → Y := fun b ↦
    if h : ∃ y, b y = true then Classical.choose h else Classical.arbitrary Y
  have hsel : Measurable sel := measurable_of_countable sel
  have heq : (fun p : Vec d × (X × Y) ↦ genHingeArgmax Δ Ψ p.1 p.2) = sel ∘ Φ := by
    funext p
    have hex : ∃ y, Φ p y = true := by
      obtain ⟨y, -, hy⟩ := Finset.exists_max_image Finset.univ
        (fun y' ↦ term Δ Ψ p.1 p.2 y') Finset.univ_nonempty
      exact ⟨y, by simpa [Φ, S] using fun y' ↦ hy y' (Finset.mem_univ _)⟩
    simp only [Function.comp, sel, dif_pos hex]
    unfold genHingeArgmax
    apply choose_congr
    funext y₀
    apply propext
    simp only [Φ, S, term, Finset.mem_univ, true_and, forall_const, Set.mem_setOf_eq,
      decide_eq_true_eq]
  rw [heq]
  exact hsel.comp hΦ

theorem measurable_direction (Δ : Y → Y → ℝ) (Ψ : X → Y → Vec d)
    (hΨ : ∀ y, Measurable (fun x ↦ Ψ x y)) :
    Measurable (Function.uncurry (genHingeDirection Δ Ψ)) := by
  have hpsi := measurable_psi Ψ hΨ
  have h1 : Measurable (fun p : Vec d × (X × Y) ↦ Ψ p.2.1 (genHingeArgmax Δ Ψ p.1 p.2)) :=
    hpsi.comp ((measurable_fst.comp measurable_snd).prodMk (measurable_argmax Δ Ψ hΨ))
  have h2 : Measurable (fun p : Vec d × (X × Y) ↦ Ψ p.2.1 p.2.2) := hpsi.comp measurable_snd
  exact h1.sub h2

end Measurability

end MulticlassSGDAux

open MulticlassSGDAux in
theorem solution {d : ℕ} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] [Fintype Y] [Nonempty Y] (Δ : Y → Y → ℝ)
    (hΔ : ∀ y' y, 0 ≤ Δ y' y) (hΔ0 : ∀ y, Δ y y = 0) (Ψ : X → Y → Vec d)
    (hΨ : ∀ y, Measurable (fun x ↦ Ψ x y)) {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B)
    (hbound : ∀ x y, ‖Ψ x y‖ ≤ ρ / 2) (D : Measure (X × Y)) [IsProbabilityMeasure D] (ε : ℝ)
    (hε : 0 < ε) (T : ℕ) (hT : B ^ 2 * ρ ^ 2 / ε ^ 2 ≤ T) :
    ∫ S, risk (deltaLoss Δ Ψ) D
        (sgdAverage (B / (ρ * Real.sqrt T)) (genHingeDirection Δ Ψ) S) ∂(iidLaw D T) ≤
      ∫ S, risk (genHingeLoss Δ Ψ) D
        (sgdAverage (B / (ρ * Real.sqrt T)) (genHingeDirection Δ Ψ) S) ∂(iidLaw D T) ∧
    ∀ u : Vec d, ‖u‖ ≤ B →
      ∫ S, risk (genHingeLoss Δ Ψ) D
          (sgdAverage (B / (ρ * Real.sqrt T)) (genHingeDirection Δ Ψ) S) ∂(iidLaw D T) ≤
        risk (genHingeLoss Δ Ψ) D u + ε := by
  set η := B / (ρ * Real.sqrt T) with hη
  set g := genHingeDirection Δ Ψ with hg_def
  have : IsProbabilityMeasure (iidLaw D T) := by unfold iidLaw; infer_instance
  set C := ⨆ p : Y × Y, Δ p.1 p.2 with hC_def
  have hlossmeas := measurable_genHinge Δ Ψ hΨ
  -- integrability of `ℓ(w, ·)`
  have hint : ∀ w, Integrable (fun z ↦ genHingeLoss Δ Ψ w z) D := by
    intro w
    refine ⟨(hlossmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := C + ρ * ‖w‖) (Filter.Eventually.of_forall fun z ↦ ?_)⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (nonneg Δ hΔ0 Ψ w z)]
    have h1 := lipschitz Δ Ψ hbound z w 0
    have h2 := le_at_zero Δ Ψ z
    rw [sub_zero] at h1
    linarith
  -- the risk is `ρ`-Lipschitz
  have hriskLip : ∀ u v, risk (genHingeLoss Δ Ψ) D u ≤
      risk (genHingeLoss Δ Ψ) D v + ρ * ‖u - v‖ := by
    intro u v
    unfold risk
    have hle : ∫ z, genHingeLoss Δ Ψ u z ∂D ≤ ∫ z, (genHingeLoss Δ Ψ v z + ρ * ‖u - v‖) ∂D :=
      integral_mono (hint u) ((hint v).add (integrable_const _))
        (fun z ↦ lipschitz Δ Ψ hbound z u v)
    rw [integral_add (hint v) (integrable_const _), integral_const] at hle
    simpa using hle
  have hriskCont : Continuous (fun w ↦ risk (genHingeLoss Δ Ψ) D w) := by
    have : LipschitzWith (Real.toNNReal ρ) (fun w ↦ risk (genHingeLoss Δ Ψ) D w) := by
      apply LipschitzWith.of_dist_le_mul
      intro u v
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hρ.le, abs_sub_le_iff]
      constructor
      · linarith [hriskLip u v]
      · have := hriskLip v u; rw [norm_sub_rev] at this; linarith
    exact this.continuous
  -- measurability of the SGD output in the sample
  have hgmeas : Measurable (Function.uncurry g) := measurable_direction Δ Ψ hΨ
  have hiter : ∀ t, Measurable (fun S : Fin T → X × Y ↦ sgdIterates η g S t) := by
    intro t
    induction t with
    | zero => exact measurable_const
    | succ t ih =>
      by_cases ht : t < T
      · have e : (fun S : Fin T → X × Y ↦ sgdIterates η g S (t + 1)) =
            fun S ↦ sgdIterates η g S t - η • g (sgdIterates η g S t) (S ⟨t, ht⟩) := by
          funext S; simp [sgdIterates, ht]
        rw [e]
        exact ih.sub ((hgmeas.comp (ih.prodMk (measurable_pi_apply _))).const_smul η)
      · have e : (fun S : Fin T → X × Y ↦ sgdIterates η g S (t + 1)) =
            fun S ↦ sgdIterates η g S t := by
          funext S; simp [sgdIterates, ht]
        rw [e]; exact ih
  have havg : Measurable (fun S : Fin T → X × Y ↦ sgdAverage η g S) := by
    unfold sgdAverage
    exact (Finset.measurable_sum (Finset.range T) (fun t _ ↦ hiter t)).const_smul ((T : ℝ)⁻¹)
  -- boundedness of the SGD output
  have hgb : ∀ w z, ‖g w z‖ ≤ ρ := fun w z ↦ by
    simp only [g, genHingeDirection]
    calc _ ≤ ‖Ψ z.1 (genHingeArgmax Δ Ψ w z)‖ + ‖Ψ z.1 z.2‖ := norm_sub_le _ _
      _ ≤ ρ / 2 + ρ / 2 := add_le_add (hbound _ _) (hbound _ _)
      _ = ρ := by ring
  have hK : 0 ≤ |η| * ρ := by positivity
  have hitb : ∀ S : Fin T → X × Y, ∀ t : ℕ, ‖sgdIterates η g S t‖ ≤ t * (|η| * ρ) := by
    intro S t
    induction t with
    | zero => simp [sgdIterates]
    | succ t ih =>
      by_cases ht : t < T
      · have e : sgdIterates η g S (t + 1) =
            sgdIterates η g S t - η • g (sgdIterates η g S t) (S ⟨t, ht⟩) := by
          simp [sgdIterates, ht]
        rw [e]
        calc _ ≤ ‖sgdIterates η g S t‖ + ‖η • g (sgdIterates η g S t) (S ⟨t, ht⟩)‖ :=
              norm_sub_le _ _
          _ ≤ t * (|η| * ρ) + |η| * ρ := by
              refine add_le_add ih ?_
              rw [norm_smul, Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_left (hgb _ _) (abs_nonneg _)
          _ = ((t + 1 : ℕ) : ℝ) * (|η| * ρ) := by push_cast; ring
      · have e : sgdIterates η g S (t + 1) = sgdIterates η g S t := by
          simp [sgdIterates, ht]
        rw [e]
        refine ih.trans ?_
        push_cast
        nlinarith
  have havgb : ∀ S : Fin T → X × Y, ‖sgdAverage η g S‖ ≤ T * (|η| * ρ) := by
    intro S
    unfold sgdAverage
    rw [norm_smul]
    rcases Nat.eq_zero_or_pos T with hT0 | hT0
    · subst hT0; simp
    · have hs : ‖∑ t ∈ Finset.range T, sgdIterates η g S t‖ ≤ T * (T * (|η| * ρ)) := by
        calc _ ≤ ∑ t ∈ Finset.range T, ‖sgdIterates η g S t‖ := norm_sum_le _ _
          _ ≤ ∑ t ∈ Finset.range T, ((T : ℝ) * (|η| * ρ)) := by
              refine Finset.sum_le_sum fun t ht ↦ (hitb S t).trans ?_
              refine mul_le_mul_of_nonneg_right ?_ hK
              exact_mod_cast (Finset.mem_range.1 ht).le
          _ = T * (T * (|η| * ρ)) := by simp
      rw [norm_inv, Real.norm_natCast]
      have hTpos : (0 : ℝ) < T := by exact_mod_cast hT0
      calc (T : ℝ)⁻¹ * ‖∑ t ∈ Finset.range T, sgdIterates η g S t‖ ≤
            (T : ℝ)⁻¹ * (T * (T * (|η| * ρ))) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = T * (|η| * ρ) := by field_simp
  have hrisk0 : risk (genHingeLoss Δ Ψ) D 0 ≤ C := by
    unfold risk
    calc ∫ z, genHingeLoss Δ Ψ 0 z ∂D ≤ ∫ _z, C ∂D :=
          integral_mono (hint 0) (integrable_const _) (fun z ↦ le_at_zero Δ Ψ z)
      _ = C := by simp
  have hint2 : Integrable (fun S ↦ risk (genHingeLoss Δ Ψ) D (sgdAverage η g S))
      (iidLaw D T) := by
    refine ⟨(hriskCont.measurable.comp havg).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := C + ρ * (T * (|η| * ρ)))
        (Filter.Eventually.of_forall fun S ↦ ?_)⟩
    have h0 : 0 ≤ risk (genHingeLoss Δ Ψ) D (sgdAverage η g S) :=
      integral_nonneg fun z ↦ nonneg Δ hΔ0 Ψ _ z
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    have h1 := hriskLip (sgdAverage η g S) 0
    have h3 := havgb S
    rw [sub_zero] at h1
    nlinarith
  have hargmax : ∀ (w : Vec d) (x : X) (y : Y),
      ⟪w, Ψ x y⟫_ℝ ≤ ⟪w, Ψ x (argmaxPredict Ψ w x)⟫_ℝ := fun w x y ↦
    (Classical.choose_spec (Finset.exists_max_image Finset.univ (fun y ↦ ⟪w, Ψ x y⟫_ℝ)
      Finset.univ_nonempty)).2 y (Finset.mem_univ _)
  refine ⟨?_, ?_⟩
  · apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun S ↦ integral_nonneg fun z ↦ hΔ _ _
    · exact hint2
    · refine Filter.Eventually.of_forall fun S ↦ ?_
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun z ↦ hΔ _ _) (hint _)
      refine Filter.Eventually.of_forall fun z ↦ ?_
      refine le_trans ?_ (term_le Δ Ψ _ z (argmaxPredict Ψ (sgdAverage η g S) z.1))
      have := hargmax (sgdAverage η g S) z.1 z.2
      simp only [term]
      rw [inner_sub_right]
      linarith
  · intro u hu
    have hprob : ConvexLipschitzBounded (Metric.closedBall (0 : Vec d) B)
        (genHingeLoss Δ Ψ) ρ B :=
      ⟨convex_closedBall _ _, fun w hw ↦ by simpa using hw, fun z ↦ convexOn Δ Ψ z,
        isLipschitzLoss Δ Ψ hbound⟩
    exact sgd_learns_convex_lipschitz (Metric.closedBall 0 B) (genHingeLoss Δ Ψ) hρ hB hprob
      hlossmeas (nonneg Δ hΔ0 Ψ) (C := C) (fun z ↦ le_at_zero Δ Ψ z) g hgmeas
      (isLossSubgradientSelector Δ Ψ) ε hε T hT D u (by simpa using hu)
