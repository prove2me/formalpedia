-- Prove2me | solution 1 for UnderstandingML.multiclass_svm_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T06:44:48.230985+00:00
-- url     : https://prove2.me/submissions/89393e59-f78c-4f24-95ca-994ca48a2dc9

import Definitions.Def_UnderstandingML_Multiclass
import Theorems.Thm_UnderstandingML_convex_lipschitz_bounded_learnable

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

namespace MulticlassSVMAux

variable {d : ℕ} {X Y : Type*} [Fintype Y] [Nonempty Y]

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

end Measurability

end MulticlassSVMAux

open MulticlassSVMAux in
theorem solution {d : ℕ} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] [Fintype Y] [Nonempty Y] (Δ : Y → Y → ℝ)
    (hΔ : ∀ y' y, 0 ≤ Δ y' y) (hΔ0 : ∀ y, Δ y y = 0) (Ψ : X → Y → Vec d)
    (hΨ : ∀ y, Measurable (fun x ↦ Ψ x y)) {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B)
    (hbound : ∀ x y, ‖Ψ x y‖ ≤ ρ / 2) (D : Measure (X × Y)) [IsProbabilityMeasure D]
    (A : Learner (X × Y) (Vec d))
    (hA : ∀ (m : ℕ) (S : Fin m → X × Y),
      IsRLM (genHingeLoss Δ Ψ) (Real.sqrt (2 * ρ ^ 2 / (B ^ 2 * m))) S (A m S))
    (hAmeas : ∀ m, Measurable (A m)) (m : ℕ) (hm : 0 < m) :
    ∫ S, risk (deltaLoss Δ Ψ) D (A m S) ∂(iidLaw D m) ≤
        ∫ S, risk (genHingeLoss Δ Ψ) D (A m S) ∂(iidLaw D m) ∧
    ∀ u : Vec d, ‖u‖ ≤ B →
      ∫ S, risk (genHingeLoss Δ Ψ) D (A m S) ∂(iidLaw D m) ≤
        risk (genHingeLoss Δ Ψ) D u + Real.sqrt (8 * ρ ^ 2 * B ^ 2 / m) := by
  set lam := Real.sqrt (2 * ρ ^ 2 / (B ^ 2 * m)) with hlam_def
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hlam : 0 < lam := Real.sqrt_pos.2 (by positivity)
  have : IsProbabilityMeasure (iidLaw D m) := by unfold iidLaw; infer_instance
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
  -- the RLM output is bounded: `λ‖A(S)‖² ≤ L_S(0) ≤ C`
  have hAb : ∀ S : Fin m → X × Y, ‖A m S‖ ≤ Real.sqrt (C / lam) := by
    intro S
    have h := hA m S 0
    unfold rlmObjective empRisk at h
    have h1 : 0 ≤ (∑ i, genHingeLoss Δ Ψ (A m S) (S i)) / m :=
      div_nonneg (Finset.sum_nonneg fun i _ ↦ nonneg Δ hΔ0 Ψ _ _) hmpos.le
    have h2 : (∑ i, genHingeLoss Δ Ψ 0 (S i)) / m ≤ C := by
      rw [div_le_iff₀ hmpos]
      calc ∑ i, genHingeLoss Δ Ψ 0 (S i) ≤ ∑ _i : Fin m, C :=
            Finset.sum_le_sum fun i _ ↦ le_at_zero Δ Ψ (S i)
        _ = C * m := by simp [mul_comm]
    have h3 : ‖A m S‖ ^ 2 ≤ C / lam := by
      rw [le_div_iff₀ hlam]
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_zero, add_zero] at h
      nlinarith
    have := Real.abs_le_sqrt h3
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hrisk0 : risk (genHingeLoss Δ Ψ) D 0 ≤ C := by
    unfold risk
    calc ∫ z, genHingeLoss Δ Ψ 0 z ∂D ≤ ∫ _z, C ∂D :=
          integral_mono (hint 0) (integrable_const _) (fun z ↦ le_at_zero Δ Ψ z)
      _ = C := by simp
  have hint2 : Integrable (fun S ↦ risk (genHingeLoss Δ Ψ) D (A m S)) (iidLaw D m) := by
    refine ⟨(hriskCont.measurable.comp (hAmeas m)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := C + ρ * Real.sqrt (C / lam))
        (Filter.Eventually.of_forall fun S ↦ ?_)⟩
    have h0 : 0 ≤ risk (genHingeLoss Δ Ψ) D (A m S) :=
      integral_nonneg fun z ↦ nonneg Δ hΔ0 Ψ _ z
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    have h1 := hriskLip (A m S) 0
    have h3 := hAb S
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
      refine le_trans ?_ (term_le Δ Ψ _ z (argmaxPredict Ψ (A m S) z.1))
      have := hargmax (A m S) z.1 z.2
      simp only [term]
      rw [inner_sub_right]
      linarith
  · intro u hu
    have hprob : ConvexLipschitzBounded (Metric.closedBall (0 : Vec d) B)
        (genHingeLoss Δ Ψ) ρ B :=
      ⟨convex_closedBall _ _, fun w hw ↦ by simpa using hw, fun z ↦ convexOn Δ Ψ z,
        isLipschitzLoss Δ Ψ hbound⟩
    have h := (convex_lipschitz_bounded_learnable (Metric.closedBall 0 B) (genHingeLoss Δ Ψ)
      hρ hB hprob A hA hlossmeas (nonneg Δ hΔ0 Ψ) (C := C) (fun z ↦ le_at_zero Δ Ψ z)
      hAmeas).1 D inferInstance m hm u (by simpa using hu)
    have e : ρ * B * Real.sqrt (8 / m) = Real.sqrt (8 * ρ ^ 2 * B ^ 2 / m) := by
      rw [show 8 * ρ ^ 2 * B ^ 2 / (m : ℝ) = (ρ * B) ^ 2 * (8 / m) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [← e]
    exact h
