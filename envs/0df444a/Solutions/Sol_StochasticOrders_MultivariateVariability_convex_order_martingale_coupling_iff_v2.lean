-- Prove2me | solution 1 for StochasticOrders.MultivariateVariability.convex_order_martingale_coupling_iff_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T03:22:05.682672+00:00
-- url     : https://prove2.me/submissions/d940d9ac-535b-4aae-91e8-f48bdd3c1a2e

import Mathlib
import Definitions.Def_StochasticOrders_MultivariateVariability_ConvexOrder

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology

/-- Convex test functions with linear growth (all integrable under first moments). -/
def CxTest8 {n : ℕ} (φ : (Fin n → ℝ) → ℝ) : Prop :=
  ConvexOn ℝ Set.univ φ ∧ ∃ C : ℝ, ∀ y, |φ y| ≤ C * (1 + ‖y‖)

/-- A martingale transport plan on `ℝⁿ × ℝⁿ`. -/
def MartPlan8 {n : ℕ} (π : Measure ((Fin n → ℝ) × (Fin n → ℝ))) : Prop :=
  Integrable Prod.fst π ∧ Integrable Prod.snd π ∧
  ∀ B : Set (Fin n → ℝ), MeasurableSet B →
    ∫ p in Prod.fst ⁻¹' B, p.2 ∂π = ∫ p in Prod.fst ⁻¹' B, p.1 ∂π

theorem cx8_cont {n : ℕ} {φ : (Fin n → ℝ) → ℝ} (hφ : ConvexOn ℝ Set.univ φ) : Continuous φ :=
  continuousOn_univ.1 (hφ.continuousOn isOpen_univ)

/-- The conditional expectation of the target given the source is the source. -/
theorem cx8_condExp {n : ℕ} (π : Measure ((Fin n → ℝ) × (Fin n → ℝ))) [IsProbabilityMeasure π]
    (h : MartPlan8 π) :
    π[Prod.snd | MeasurableSpace.comap (Prod.fst : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ))
      inferInstance] =ᵐ[π] Prod.fst := by
  obtain ⟨h1, h2, h3⟩ := h
  have hm : MeasurableSpace.comap (Prod.fst : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ))
      inferInstance ≤ (inferInstance : MeasurableSpace ((Fin n → ℝ) × (Fin n → ℝ))) :=
    measurable_fst.comap_le
  have hfm : Measurable[MeasurableSpace.comap
      (Prod.fst : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)) inferInstance]
      (Prod.fst : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)) := Measurable.of_comap_le le_rfl
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hm h2 ?_ ?_
    hfm.stronglyMeasurable.aestronglyMeasurable
  · intro s _ _
    exact h1.integrableOn
  · intro s hs _
    obtain ⟨B, hB, rfl⟩ := hs
    exact (h3 B hB).symm

/-- (⇐) conditional Jensen. -/
theorem cx8_converse {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {n : ℕ} (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ)
    (hYint : Integrable Y ν)
    {Ω'' : Type} [MeasurableSpace Ω''] (ρ : Measure Ω'') [IsProbabilityMeasure ρ]
    (Xhat Yhat : Ω'' → Fin n → ℝ) (hXh : Measurable Xhat)
    (hIX : IdentDistrib Xhat X ρ μ) (hIY : IdentDistrib Yhat Y ρ ν)
    (hmart : ρ[Yhat | MeasurableSpace.comap Xhat inferInstance] =ᵐ[ρ] Xhat) :
    StochasticOrders.MultivariateVariability.ConvexOrder μ ν X Y := by
  intro φ hφ hφX hφY
  have hcont : Continuous φ := cx8_cont hφ
  have hm : MeasurableSpace.comap Xhat inferInstance ≤ (inferInstance : MeasurableSpace Ω'') :=
    hXh.comap_le
  have hIXφ := hIX.comp hcont.measurable
  have hIYφ := hIY.comp hcont.measurable
  have hYh : Integrable Yhat ρ := hIY.integrable_iff.2 hYint
  have hφYh : Integrable (φ ∘ Yhat) ρ := hIYφ.integrable_iff.2 hφY
  have hφXh : Integrable (φ ∘ Xhat) ρ := hIXφ.integrable_iff.2 hφX
  show ∫ ω, (φ ∘ X) ω ∂μ ≤ ∫ ω, (φ ∘ Y) ω ∂ν
  rw [← hIXφ.integral_eq, ← hIYφ.integral_eq]
  have hJ := hφ.map_condExp_le_univ hm hcont.lowerSemicontinuous hYh hφYh
  have h1 : (φ ∘ Xhat) ≤ᵐ[ρ] ρ[φ ∘ Yhat | MeasurableSpace.comap Xhat inferInstance] := by
    filter_upwards [hJ, hmart] with ω h1 h2
    simpa [Function.comp, h2] using h1
  calc ∫ ω, (φ ∘ Xhat) ω ∂ρ ≤ ∫ ω, (ρ[φ ∘ Yhat | MeasurableSpace.comap Xhat inferInstance]) ω ∂ρ :=
        integral_mono_ae hφXh integrable_condExp h1
    _ = ∫ ω, (φ ∘ Yhat) ω ∂ρ := integral_condExp hm

/-- Jensen along a martingale plan. -/
theorem cx8_jensen {n : ℕ} (π : Measure ((Fin n → ℝ) × (Fin n → ℝ))) [IsProbabilityMeasure π]
    (hπ : MartPlan8 π) (φ : (Fin n → ℝ) → ℝ) (hφ : ConvexOn ℝ Set.univ φ)
    (h1 : Integrable (fun p => φ p.1) π) (h2 : Integrable (fun p => φ p.2) π) :
    ∫ p, φ p.1 ∂π ≤ ∫ p, φ p.2 ∂π :=
  cx8_converse π π Prod.fst Prod.snd hπ.2.1 π Prod.fst Prod.snd measurable_fst
    (IdentDistrib.refl measurable_fst.aemeasurable)
    (IdentDistrib.refl measurable_snd.aemeasurable) (cx8_condExp π hπ) φ hφ h1 h2

/-- The random-vector witness from a martingale plan between the laws. -/
theorem cx8_witness {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {n : ℕ}
    (μ : Measure Ω) (ν : Measure Ω') (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (π : Measure ((Fin n → ℝ) × (Fin n → ℝ))) [IsProbabilityMeasure π] (hπ : MartPlan8 π)
    (h1 : π.map Prod.fst = μ.map X) (h2 : π.map Prod.snd = ν.map Y) :
    ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → Fin n → ℝ),
        Measurable Xhat ∧ Measurable Yhat ∧
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧
        ρ[Yhat | MeasurableSpace.comap Xhat inferInstance] =ᵐ[ρ] Xhat :=
  ⟨_, inferInstance, π, inferInstance, Prod.fst, Prod.snd, measurable_fst, measurable_snd,
    ⟨measurable_fst.aemeasurable, hX.aemeasurable, h1⟩,
    ⟨measurable_snd.aemeasurable, hY.aemeasurable, h2⟩, cx8_condExp π hπ⟩

/-- Test functions are integrable under first moments. -/
theorem cx8_test_int {n : ℕ} (m : Measure (Fin n → ℝ)) [IsFiniteMeasure m]
    (hm : Integrable id m) (φ : (Fin n → ℝ) → ℝ) (hφ : CxTest8 φ) : Integrable φ m := by
  obtain ⟨hc, C, hC⟩ := hφ
  refine Integrable.mono' ((integrable_const C).add (hm.norm.const_mul C))
    (cx8_cont hc).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply, id]
  calc |φ y| ≤ C * (1 + ‖y‖) := hC y
    _ = C + C * ‖y‖ := by ring

/-- The convex order of the vectors gives the test-function order of the laws. -/
theorem cx8_order_laws {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {n : ℕ}
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXi : Integrable X μ) (hYi : Integrable Y ν)
    (h : StochasticOrders.MultivariateVariability.ConvexOrder μ ν X Y)
    (φ : (Fin n → ℝ) → ℝ) (hφ : CxTest8 φ) :
    ∫ x, φ x ∂(μ.map X) ≤ ∫ y, φ y ∂(ν.map Y) := by
  have : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have : IsProbabilityMeasure (ν.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hcont : Continuous φ := cx8_cont hφ.1
  have i1 : Integrable id (μ.map X) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hX.aemeasurable).2 hXi
  have i2 : Integrable id (ν.map Y) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hY.aemeasurable).2 hYi
  have e1 : Integrable (φ ∘ X) μ :=
    (integrable_map_measure hcont.aestronglyMeasurable hX.aemeasurable).1 (cx8_test_int _ i1 φ hφ)
  have e2 : Integrable (φ ∘ Y) ν :=
    (integrable_map_measure hcont.aestronglyMeasurable hY.aemeasurable).1 (cx8_test_int _ i2 φ hφ)
  rw [integral_map hX.aemeasurable hcont.aestronglyMeasurable,
    integral_map hY.aemeasurable hcont.aestronglyMeasurable]
  exact h φ hφ.1 e1 e2

/-- Slot `l` of the moment space, carrying mass `1` and first moment `y`. -/
noncomputable def slot8 {n m : ℕ} (l : Fin m) (y : Fin n → ℝ) :
    (Fin m → ℝ) × (Fin m → Fin n → ℝ) :=
  (Pi.single l 1, Pi.single l y)

theorem slot8_cont {n m : ℕ} (l : Fin m) : Continuous (slot8 (n := n) l) := by
  unfold slot8
  refine continuous_const.prodMk ?_
  exact (ContinuousLinearMap.single ℝ (fun _ : Fin m => Fin n → ℝ) l).continuous

theorem slot8_norm {n m : ℕ} (l : Fin m) (y : Fin n → ℝ) : ‖slot8 l y‖ ≤ 1 + ‖y‖ := by
  have hs : ∀ {F : Type} [NormedAddCommGroup F] (x : F), ‖(Pi.single l x : Fin m → F)‖ ≤ ‖x‖ := by
    intro F _ x
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun k => ?_
    by_cases h : k = l
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [Prod.norm_def]
  refine max_le ((hs (1 : ℝ)).trans ?_) ((hs y).trans ?_)
  · simp
  · linarith

theorem slot8_affine {n m : ℕ} (l : Fin m) (x y : Fin n → ℝ) (a b : ℝ) (hab : a + b = 1) :
    slot8 l (a • x + b • y) = a • slot8 l x + b • slot8 l y := by
  ext k j
  · by_cases h : k = l
    · subst h; simp [slot8, ← add_mul, hab]
    · simp [slot8, Pi.single_apply, h]
  · by_cases h : k = l
    · subst h; simp [slot8]
    · simp [slot8, Pi.single_apply, h]

/-- Semi-discrete approximate Strassen: a finitely supported source dominated in the test order
by an integrable target admits selections with nearly the right masses and first moments. -/
theorem cx8_semidiscrete {n m : ℕ} (hm : 0 < m) (β : Measure (Fin n → ℝ))
    [IsProbabilityMeasure β] (hβ : Integrable id β) (p : Fin m → ℝ) (a : Fin m → Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hord : ∀ φ, CxTest8 φ → ∑ i, p i * φ (a i) ≤ ∫ y, φ y ∂β) (ε : ℝ) (hε : 0 < ε) :
    ∃ θ : Fin m → (Fin n → ℝ) → ℝ, (∀ l, Measurable (θ l)) ∧ (∀ l y, 0 ≤ θ l y) ∧
      (∀ y, ∑ l, θ l y = 1) ∧
      ∀ l, |∫ y, θ l y ∂β - p l| < ε ∧ ‖∫ y, θ l y • y ∂β - p l • a l‖ < ε := by
  classical
  let Sel : Set (Fin m → (Fin n → ℝ) → ℝ) :=
    {θ | (∀ l, Measurable (θ l)) ∧ (∀ l y, 0 ≤ θ l y) ∧ (∀ y, ∑ l, θ l y = 1)}
  let P : (Fin m → (Fin n → ℝ) → ℝ) → (Fin m → ℝ) × (Fin m → Fin n → ℝ) :=
    fun θ => ∫ y, ∑ l, θ l y • slot8 l y ∂β
  have hint : ∀ θ ∈ Sel, Integrable (fun y => ∑ l, θ l y • slot8 l y) β := by
    intro θ hθ
    refine integrable_finsetSum _ fun l _ => ?_
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hβ.norm)
      (((hθ.1 l).smul (slot8_cont l).measurable).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    have h1 : θ l y ≤ 1 := by
      rw [← hθ.2.2 y]
      exact Finset.single_le_sum (fun k _ => hθ.2.1 k y) (Finset.mem_univ l)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hθ.2.1 l y)]
    simp only [Pi.add_apply, id]
    calc θ l y * ‖slot8 l y‖ ≤ 1 * (1 + ‖y‖) :=
          mul_le_mul h1 (slot8_norm l y) (norm_nonneg _) zero_le_one
      _ = 1 + ‖y‖ := one_mul _
  have hconv : Convex ℝ (P '' Sel) := by
    rintro _ ⟨θ1, h1, rfl⟩ _ ⟨θ2, h2, rfl⟩ a b ha hb hab
    refine ⟨fun l y => a * θ1 l y + b * θ2 l y,
      ⟨fun l => ((h1.1 l).const_mul a).add ((h2.1 l).const_mul b), fun l y => ?_, fun y => ?_⟩, ?_⟩
    · have := h1.2.1 l y
      have := h2.2.1 l y
      positivity
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1.2.2 y, h2.2.2 y]
      linarith
    · show ∫ y, ∑ l, (a * θ1 l y + b * θ2 l y) • slot8 l y ∂β = a • P θ1 + b • P θ2
      have e : (fun y => ∑ l, (a * θ1 l y + b * θ2 l y) • slot8 l y) =
          fun y => a • (∑ l, θ1 l y • slot8 l y) + b • (∑ l, θ2 l y • slot8 l y) := by
        funext y
        simp only [Finset.smul_sum, smul_smul, add_smul, Finset.sum_add_distrib]
      rw [e, integral_add (f := fun y => a • (∑ l, θ1 l y • slot8 l y))
        (g := fun y => b • (∑ l, θ2 l y • slot8 l y))
        ((hint θ1 h1).smul a) ((hint θ2 h2).smul b), integral_smul, integral_smul]
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  let t : (Fin m → ℝ) × (Fin m → Fin n → ℝ) := ∑ i, p i • slot8 i (a i)
  have key : t ∈ closure (P '' Sel) := by
    by_contra hnot
    obtain ⟨f, u, hfS, hft⟩ :=
      geometric_hahn_banach_closed_point hconv.closure isClosed_closure hnot
    let g : Fin m → (Fin n → ℝ) → ℝ := fun l y => f (slot8 l y)
    have hgm : ∀ k, Measurable (g k) := fun k => (f.continuous.comp (slot8_cont k)).measurable
    let φ : (Fin n → ℝ) → ℝ := fun y => Finset.univ.sup' hne fun l => g l y
    have hb : ∀ l y, |g l y| ≤ ‖f‖ * (1 + ‖y‖) := by
      intro l y
      have := f.le_opNorm (slot8 l y)
      rw [Real.norm_eq_abs] at this
      exact this.trans (mul_le_mul_of_nonneg_left (slot8_norm l y) (norm_nonneg _))
    have hφ : CxTest8 φ := by
      refine ⟨⟨convex_univ, fun x _ y _ a b ha hb' hab => ?_⟩, ‖f‖, fun y => abs_le.2 ⟨?_, ?_⟩⟩
      · obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_sup' hne fun l => g l (a • x + b • y)
        simp only [φ]
        rw [hl]
        simp only [g, slot8_affine l x y a b hab, map_add, map_smul, smul_eq_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (Finset.le_sup' (fun l => g l x)
          (Finset.mem_univ l)) ha) (mul_le_mul_of_nonneg_left (Finset.le_sup' (fun l => g l y)
          (Finset.mem_univ l)) hb')
      · exact (neg_le_of_abs_le (hb ⟨0, hm⟩ y)).trans
          (Finset.le_sup' (fun l => g l y) (Finset.mem_univ _))
      · exact Finset.sup'_le _ _ fun l _ => (le_abs_self _).trans (hb l y)
    -- smallest-index argmax selection
    let T : Fin m → Set (Fin n → ℝ) := fun l =>
      {y | (∀ k, g k y ≤ g l y) ∧ ∀ k, k < l → g k y < g l y}
    have hTm : ∀ l, MeasurableSet (T l) := by
      intro l
      have : T l = (⋂ k, {y | g k y ≤ g l y}) ∩
          ⋂ k, ⋂ (_ : k < l), {y | g k y < g l y} := by
        ext y; simp [T]
      rw [this]
      exact (MeasurableSet.iInter fun k => measurableSet_le (hgm k) (hgm l)).inter
        (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
          measurableSet_lt (hgm k) (hgm l))
    have hT : ∀ y, ∃ l0, y ∈ T l0 ∧ ∀ l, y ∈ T l → l = l0 := by
      intro y
      let A := Finset.univ.filter fun l => ∀ k, g k y ≤ g l y
      have hA : A.Nonempty := by
        obtain ⟨l, -, hl⟩ := Finset.exists_max_image Finset.univ (fun l => g l y) hne
        exact ⟨l, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun k => hl k (Finset.mem_univ _)⟩⟩
      have h0 := Finset.mem_filter.1 (A.min'_mem hA)
      have hmem : y ∈ T (A.min' hA) := by
        refine ⟨h0.2, fun k hk => lt_of_le_of_ne (h0.2 k) fun heq => ?_⟩
        have : k ∈ A := Finset.mem_filter.2 ⟨Finset.mem_univ _, fun k' => heq ▸ h0.2 k'⟩
        exact absurd (A.min'_le k this) (not_le.2 hk)
      refine ⟨A.min' hA, hmem, fun l hl => ?_⟩
      rcases lt_trichotomy l (A.min' hA) with h | h | h
      · exact absurd (hl.1 _) (not_le.2 (hmem.2 l h))
      · exact h
      · exact absurd (h0.2 l) (not_le.2 (hl.2 _ h))
    let θs : Fin m → (Fin n → ℝ) → ℝ := fun l y => if y ∈ T l then 1 else 0
    have hsel : θs ∈ Sel := by
      refine ⟨fun l => Measurable.ite (hTm l) measurable_const measurable_const,
        fun l y => by simp only [θs]; split_ifs <;> norm_num, fun y => ?_⟩
      obtain ⟨l0, h0, hu⟩ := hT y
      rw [Finset.sum_eq_single l0]
      · simp [θs, h0]
      · intro b _ hb
        simp [θs, show y ∉ T b from fun h => hb (hu b h)]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hval : ∀ y, f (∑ l, θs l y • slot8 l y) = φ y := by
      intro y
      obtain ⟨l0, h0, hu⟩ := hT y
      rw [map_sum, Finset.sum_eq_single l0]
      · simp only [θs, if_pos h0, one_smul]
        exact le_antisymm (Finset.le_sup' (fun l => g l y) (Finset.mem_univ l0))
          (Finset.sup'_le _ _ fun k _ => h0.1 k)
      · intro b _ hb
        simp [θs, show y ∉ T b from fun h => hb (hu b h)]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hfP : f (P θs) = ∫ y, φ y ∂β := by
      simp only [P]
      rw [← f.integral_comp_comm (hint θs hsel)]
      exact integral_congr_ae (Eventually.of_forall hval)
    have hft' : f t ≤ ∫ y, φ y ∂β := by
      calc f t = ∑ i, p i * g i (a i) := by
            simp only [t, map_sum, map_smul, smul_eq_mul, g]
        _ ≤ ∑ i, p i * φ (a i) := Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (Finset.le_sup' (fun l => g l (a i))
              (Finset.mem_univ i)) (hp i)
        _ ≤ ∫ y, φ y ∂β := hord φ hφ
    have h1 := hfS (P θs) (subset_closure ⟨θs, hsel, rfl⟩)
    linarith
  obtain ⟨v, ⟨θ, hθ, rfl⟩, hv⟩ := Metric.mem_closure_iff.1 key ε hε
  refine ⟨θ, hθ.1, hθ.2.1, hθ.2.2, fun l => ⟨?_, ?_⟩⟩
  · let L1 : (Fin m → ℝ) × (Fin m → Fin n → ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj l).comp (ContinuousLinearMap.fst ℝ _ _)
    have e1 : (P θ).1 l = ∫ y, θ l y ∂β := by
      show L1 (P θ) = _
      simp only [P]
      rw [← L1.integral_comp_comm (hint θ hθ)]
      congr 1; funext y
      simp [L1, slot8, Pi.single_apply]
    have e2 : t.1 l = p l := by
      simp [t, slot8, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    rw [← e1, ← e2]
    calc |(P θ).1 l - t.1 l| = ‖(P θ - t).1 l‖ := by simp [Real.norm_eq_abs]
      _ ≤ ‖(P θ - t).1‖ := norm_le_pi_norm _ l
      _ ≤ ‖P θ - t‖ := norm_fst_le _
      _ < ε := by rw [← dist_eq_norm, dist_comm]; exact hv
  · let L2 : (Fin m → ℝ) × (Fin m → Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
      (ContinuousLinearMap.proj l).comp (ContinuousLinearMap.snd ℝ _ _)
    have e1 : (P θ).2 l = ∫ y, θ l y • y ∂β := by
      show L2 (P θ) = _
      simp only [P]
      rw [← L2.integral_comp_comm (hint θ hθ)]
      congr 1; funext y
      simp [L2, slot8, Pi.single_apply]
    have e2 : t.2 l = p l • a l := by
      simp [t, slot8, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    rw [← e1, ← e2]
    calc ‖(P θ).2 l - t.2 l‖ = ‖(P θ - t).2 l‖ := by simp
      _ ≤ ‖(P θ - t).2‖ := norm_le_pi_norm _ l
      _ ≤ ‖P θ - t‖ := norm_snd_le _
      _ < ε := by rw [← dist_eq_norm, dist_comm]; exact hv

theorem cx8_int_aux {n : ℕ} (β : Measure (Fin n → ℝ)) [IsProbabilityMeasure β]
    (hβ : Integrable id β) (θ : (Fin n → ℝ) → ℝ) (hθm : Measurable θ) (h0 : ∀ y, 0 ≤ θ y)
    (h1 : ∀ y, θ y ≤ 1) {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (H : (Fin n → ℝ) → G) (hH : AEStronglyMeasurable H β) (c : ℝ) (hc : ∀ y, ‖H y‖ ≤ c + ‖y‖) :
    Integrable (fun y => θ y • H y) β := by
  refine Integrable.mono' ((integrable_const c).add hβ.norm)
    (hθm.aestronglyMeasurable.smul hH) (Eventually.of_forall fun y => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (h0 y)]
  simp only [Pi.add_apply, id]
  exact (mul_le_of_le_one_left (norm_nonneg _) (h1 y)).trans (hc y)

theorem cx8_int_aux2 {n : ℕ} (β : Measure (Fin n → ℝ)) [IsProbabilityMeasure β]
    (hβ : Integrable id β) (θ : (Fin n → ℝ) → ℝ) (hθm : Measurable θ) (h0 : ∀ y, 0 ≤ θ y)
    (h1 : ∀ y, θ y ≤ 1) {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (H : (Fin n → ℝ) → G) (hH : AEStronglyMeasurable H β) (c c' : ℝ)
    (hc : ∀ y, ‖H y‖ ≤ c + c' * ‖y‖) :
    Integrable (fun y => θ y • H y) β := by
  refine Integrable.mono' ((integrable_const c).add (hβ.norm.const_mul c'))
    (hθm.aestronglyMeasurable.smul hH) (Eventually.of_forall fun y => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (h0 y)]
  simp only [Pi.add_apply, id]
  exact (mul_le_of_le_one_left (norm_nonneg _) (h1 y)).trans (hc y)

theorem cx8_comp {n : ℕ} (β : Measure (Fin n → ℝ)) (θ : (Fin n → ℝ) → ℝ) (hθm : Measurable θ)
    (h0 : ∀ y, 0 ≤ θ y) (b : Fin n → ℝ) {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : (Fin n → ℝ) × (Fin n → ℝ) → G) (hF : StronglyMeasurable F) :
    (Integrable F ((β.withDensity (fun y => ((θ y).toNNReal : ENNReal))).map (fun y => (b, y))) ↔
      Integrable (fun y => θ y • F (b, y)) β) ∧
    ∫ p, F p ∂((β.withDensity (fun y => ((θ y).toNNReal : ENNReal))).map (fun y => (b, y))) =
      ∫ y, θ y • F (b, y) ∂β := by
  have hmeas : Measurable (fun y : Fin n → ℝ => (b, y)) := measurable_const.prodMk measurable_id
  have hw : Measurable (fun y => (θ y).toNNReal) := hθm.real_toNNReal
  have e : (fun y => (θ y).toNNReal • (F ∘ fun y => (b, y)) y) = fun y => θ y • F (b, y) := by
    funext y
    rw [NNReal.smul_def, Real.coe_toNNReal _ (h0 y)]
    rfl
  constructor
  · rw [integrable_map_measure hF.aestronglyMeasurable hmeas.aemeasurable,
      integrable_withDensity_iff_integrable_smul hw, e]
  · rw [integral_map hmeas.aemeasurable hF.aestronglyMeasurable,
      integral_withDensity_eq_integral_smul hw]
    exact congrArg (fun h => ∫ y, h y ∂β) e

/-- The martingale plan of a selection: atoms at the barycentres `b_l = r_l / q_l`. -/
theorem cx8_plan {n m : ℕ} (β : Measure (Fin n → ℝ)) [IsProbabilityMeasure β]
    (hβ : Integrable id β) (θ : Fin m → (Fin n → ℝ) → ℝ) (hθm : ∀ l, Measurable (θ l))
    (hθ0 : ∀ l y, 0 ≤ θ l y) (hθ1 : ∀ y, ∑ l, θ l y = 1) :
    ∃ π : Measure ((Fin n → ℝ) × (Fin n → ℝ)), IsProbabilityMeasure π ∧ MartPlan8 π ∧
      π.map Prod.snd = β ∧
      (∀ g : (Fin n → ℝ) → ℝ, Measurable g → (∃ C, ∀ x, |g x| ≤ C) → ∀ j : Fin n,
        ∫ p, g p.1 * (p.2 j - p.1 j) ∂π = 0) ∧
      ∃ b : Fin m → (Fin n → ℝ), (∀ l, (∫ y, θ l y ∂β) • b l = ∫ y, θ l y • y ∂β) ∧
      ∀ g : (Fin n → ℝ) → ℝ, Measurable g → (∃ C, ∀ x, |g x| ≤ C) →
        ∫ p, g p.1 ∂π = ∑ l, (∫ y, θ l y ∂β) * g (b l) := by
  classical
  set q : Fin m → ℝ := fun l => ∫ y, θ l y ∂β with hq
  set r : Fin m → (Fin n → ℝ) := fun l => ∫ y, θ l y • y ∂β with hr
  set b : Fin m → (Fin n → ℝ) := fun l => (q l)⁻¹ • r l with hb
  have hle : ∀ l y, θ l y ≤ 1 := fun l y => by
    rw [← hθ1 y]
    exact Finset.single_le_sum (fun k _ => hθ0 k y) (Finset.mem_univ l)
  let M : Fin m → Measure ((Fin n → ℝ) × (Fin n → ℝ)) := fun l =>
    (β.withDensity (fun y => ((θ l y).toNNReal : ENNReal))).map (fun y => (b l, y))
  let π := ∑ l, M l
  have hθint : ∀ l, Integrable (θ l) β := by
    intro l
    have := cx8_int_aux β hβ (θ l) (hθm l) (hθ0 l) (hle l) (fun _ => (1 : ℝ))
      aestronglyMeasurable_const 1 (fun y => by simp)
    simpa using this
  have hqb : ∀ l, q l • b l = r l := by
    intro l
    by_cases h : q l = 0
    · have hz : θ l =ᵐ[β] 0 := (integral_eq_zero_iff_of_nonneg (fun y => hθ0 l y) (hθint l)).1 h
      have : r l = 0 := by
        simp only [hr]
        rw [integral_congr_ae (hz.mono fun y hy => by simp [hy] : (fun y => θ l y • y) =ᵐ[β] 0)]
        simp
      rw [this, h, zero_smul]
    · simp only [hb]
      rw [smul_smul, mul_inv_cancel₀ h, one_smul]
  -- integration against π
  have hπint : ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
      (F : (Fin n → ℝ) × (Fin n → ℝ) → G), StronglyMeasurable F →
      (∀ l, Integrable (fun y => θ l y • F (b l, y)) β) →
      Integrable F π ∧ ∫ p, F p ∂π = ∑ l, ∫ y, θ l y • F (b l, y) ∂β := by
    intro G _ _ F hF hI
    have hI' : ∀ l ∈ (Finset.univ : Finset (Fin m)), Integrable F (M l) :=
      fun l _ => (cx8_comp β (θ l) (hθm l) (hθ0 l) (b l) F hF).1.2 (hI l)
    refine ⟨integrable_finsetSum_measure.2 hI', ?_⟩
    rw [integral_finsetSum_measure hI']
    exact Finset.sum_congr rfl fun l _ => (cx8_comp β (θ l) (hθm l) (hθ0 l) (b l) F hF).2
  have hsnd : π.map Prod.snd = β := by
    ext A hA
    rw [Measure.map_apply measurable_snd hA]
    simp only [π, M, Measure.coe_finsetSum, Finset.sum_apply]
    have hmeas : ∀ l, Measurable (fun y : Fin n → ℝ => (b l, y)) :=
      fun l => measurable_const.prodMk measurable_id
    have e : ∀ l, (Measure.map (fun y => (b l, y))
        (β.withDensity fun y => ((θ l y).toNNReal : ENNReal))) (Prod.snd ⁻¹' A) =
        ∫⁻ y in A, ((θ l y).toNNReal : ENNReal) ∂β := by
      intro l
      rw [Measure.map_apply (hmeas l) (measurable_snd hA)]
      exact withDensity_apply _ hA
    rw [Finset.sum_congr rfl fun l _ => e l]
    rw [← lintegral_finset_sum _ (fun l _ => (hθm l).real_toNNReal.coe_nnreal_ennreal)]
    have h1 : ∀ y, ∑ l, ((θ l y).toNNReal : ENNReal) = 1 := by
      intro y
      rw [← ENNReal.coe_finset_sum, ← Real.toNNReal_sum_of_nonneg (fun l _ => hθ0 l y), hθ1 y]
      simp
    simp_rw [h1]
    simp
  have hprob : IsProbabilityMeasure π := by
    constructor
    have := congrArg (fun ν : Measure (Fin n → ℝ) => ν Set.univ) hsnd
    rw [Measure.map_apply measurable_snd MeasurableSet.univ, Set.preimage_univ] at this
    rw [this, measure_univ]
  have hfstI := hπint (fun p => p.1) measurable_fst.stronglyMeasurable fun l =>
    cx8_int_aux β hβ (θ l) (hθm l) (hθ0 l) (hle l) (fun _ => b l) aestronglyMeasurable_const
      ‖b l‖ (fun y => by simp)
  have hsndI := hπint (fun p => p.2) measurable_snd.stronglyMeasurable fun l =>
    cx8_int_aux β hβ (θ l) (hθm l) (hθ0 l) (hle l) (fun y => y) aestronglyMeasurable_id
      0 (fun y => by simp)
  have hmart : ∀ g : (Fin n → ℝ) → ℝ, Measurable g → (∃ C, ∀ x, |g x| ≤ C) → ∀ j : Fin n,
      ∫ p, g p.1 * (p.2 j - p.1 j) ∂π = 0 := by
    intro g hg ⟨C, hC⟩ j
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    have hF : StronglyMeasurable
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) => g p.1 * (p.2 j - p.1 j)) :=
      ((hg.comp measurable_fst).mul (((measurable_pi_apply j).comp measurable_snd).sub
        ((measurable_pi_apply j).comp measurable_fst))).stronglyMeasurable
    have hI : ∀ l, Integrable (fun y => θ l y •
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) => g p.1 * (p.2 j - p.1 j)) (b l, y)) β := by
      intro l
      refine cx8_int_aux2 β hβ (θ l) (hθm l) (hθ0 l) (hle l) _
        ((hF.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
        (C * ‖b l‖) C (fun y => ?_)
      simp only [Real.norm_eq_abs, abs_mul]
      have h1 : |y j - b l j| ≤ ‖y‖ + ‖b l‖ := by
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · exact (Real.norm_eq_abs (y j)) ▸ norm_le_pi_norm y j
        · exact (Real.norm_eq_abs (b l j)) ▸ norm_le_pi_norm (b l) j
      calc |g (b l)| * |y j - b l j| ≤ C * (‖y‖ + ‖b l‖) :=
            mul_le_mul (hC _) h1 (abs_nonneg _) hC0
        _ = C * ‖b l‖ + C * ‖y‖ := by ring
    rw [(hπint _ hF hI).2]
    refine Finset.sum_eq_zero fun l _ => ?_
    have hyI : Integrable (fun y => θ l y • y) β :=
      cx8_int_aux β hβ (θ l) (hθm l) (hθ0 l) (hle l) (fun y => y) aestronglyMeasurable_id 0
        (fun y => by simp)
    have hr' : ∫ y, (θ l y • y) j ∂β = r l j := by
      have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).integral_comp_comm hyI
      simpa using this
    have hqj : q l * b l j = r l j := by
      have := congrFun (hqb l) j
      simpa using this
    have hq' : ∫ y, θ l y ∂β = q l := rfl
    simp only [smul_eq_mul]
    calc ∫ y, θ l y * (g (b l) * (y j - b l j)) ∂β
        = ∫ y, (g (b l) * (θ l y • y) j - (g (b l) * b l j) * θ l y) ∂β := by
          congr 1; funext y; simp only [Pi.smul_apply, smul_eq_mul]; ring
      _ = g (b l) * ∫ y, (θ l y • y) j ∂β - (g (b l) * b l j) * ∫ y, θ l y ∂β := by
          rw [integral_sub, integral_const_mul, integral_const_mul]
          · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).integrable_comp
              hyI).const_mul _
          · exact (hθint l).const_mul _
      _ = 0 := by rw [hr', hq', ← hqj]; ring
  refine ⟨π, hprob, ⟨hfstI.1, hsndI.1, fun B hB => ?_⟩, hsnd, hmart, b, hqb,
    fun g hg ⟨C, hC⟩ => ?_⟩
  · have hBm : MeasurableSet (Prod.fst ⁻¹' B : Set ((Fin n → ℝ) × (Fin n → ℝ))) := measurable_fst hB
    rw [← integral_indicator hBm, ← integral_indicator hBm]
    have hI2 := hπint ((Prod.fst ⁻¹' B).indicator fun p => p.2)
      (measurable_snd.indicator hBm).stronglyMeasurable fun l => by
        refine cx8_int_aux β hβ (θ l) (hθm l) (hθ0 l) (hle l) _
          ((measurable_snd.indicator hBm).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
          0 (fun y => ?_)
        by_cases h : b l ∈ B <;> simp [Set.indicator, h] <;> positivity
    have hI1 := hπint ((Prod.fst ⁻¹' B).indicator fun p => p.1)
      (measurable_fst.indicator hBm).stronglyMeasurable fun l => by
        refine cx8_int_aux β hβ (θ l) (hθm l) (hθ0 l) (hle l) _
          ((measurable_fst.indicator hBm).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
          ‖b l‖ (fun y => ?_)
        by_cases h : b l ∈ B <;> simp [Set.indicator, h] <;> positivity
    rw [hI2.2, hI1.2]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h : b l ∈ B
    · simp only [Set.indicator, Set.mem_preimage, h, if_true]
      rw [integral_smul_const]
      exact (hqb l).symm
    · simp [Set.indicator, h]
  · have hgI := hπint (fun p => g p.1) (hg.comp measurable_fst).stronglyMeasurable fun l =>
      cx8_int_aux β hβ (θ l) (hθm l) (hθ0 l) (hle l) (fun _ => g (b l)) aestronglyMeasurable_const
        C (fun y => by simp only [Real.norm_eq_abs]; linarith [hC (b l), norm_nonneg y])
    rw [hgI.2]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [smul_eq_mul]
    rw [integral_mul_const]

/-- Cluster point of plans with fixed second marginal and convergent first marginals. -/
theorem cx8_cluster {n : ℕ} (α β : Measure (Fin n → ℝ)) [IsProbabilityMeasure α]
    [IsProbabilityMeasure β] (πk : ℕ → Measure ((Fin n → ℝ) × (Fin n → ℝ)))
    (hπ : ∀ k, IsProbabilityMeasure (πk k) ∧ (πk k).map Prod.snd = β)
    (hconv : ∀ g : BoundedContinuousFunction (Fin n → ℝ) ℝ,
      Tendsto (fun k => ∫ p, g p.1 ∂(πk k)) atTop (𝓝 (∫ x, g x ∂α))) :
    ∃ π : Measure ((Fin n → ℝ) × (Fin n → ℝ)), IsProbabilityMeasure π ∧
      π.map Prod.fst = α ∧ π.map Prod.snd = β ∧
      ∀ (F : BoundedContinuousFunction ((Fin n → ℝ) × (Fin n → ℝ)) ℝ) (c : ℝ),
        (∀ k, |∫ p, F p ∂(πk k)| ≤ c) → |∫ p, F p ∂π| ≤ c := by
  classical
  let Pk : ℕ → ProbabilityMeasure ((Fin n → ℝ) × (Fin n → ℝ)) := fun k => ⟨πk k, (hπ k).1⟩
  let μP : ProbabilityMeasure (Fin n → ℝ) := ⟨α, inferInstance⟩
  let νP : ProbabilityMeasure (Fin n → ℝ) := ⟨β, inferInstance⟩
  let μkP : ℕ → ProbabilityMeasure (Fin n → ℝ) := fun k =>
    ⟨(πk k).map Prod.fst, by
      have := (hπ k).1
      exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable⟩
  have tμ : Tendsto μkP atTop (𝓝 μP) := by
    refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun g => ?_
    have e : (fun k => ∫ x, g x ∂((μkP k : ProbabilityMeasure (Fin n → ℝ)) : Measure (Fin n → ℝ)))
        = fun k => ∫ p, g p.1 ∂(πk k) := funext fun k =>
      integral_map measurable_fst.aemeasurable g.continuous.aestronglyMeasurable
    rw [e]
    exact hconv g
  have tight_of : ∀ (Qs : ℕ → ProbabilityMeasure (Fin n → ℝ)) (Q : ProbabilityMeasure (Fin n → ℝ)),
      Tendsto Qs atTop (𝓝 Q) →
      IsTightMeasureSet {((P : ProbabilityMeasure (Fin n → ℝ)) : Measure (Fin n → ℝ)) |
        P ∈ Set.range Qs} := by
    intro Qs Q hQ
    apply isTightMeasureSet_of_isCompact_closure
    have hc := hQ.isCompact_insert_range
    exact hc.of_isClosed_subset isClosed_closure
      (closure_minimal (Set.subset_insert _ _) hc.isClosed)
  have tightπ : IsTightMeasureSet {((P : ProbabilityMeasure ((Fin n → ℝ) × (Fin n → ℝ))) :
      Measure ((Fin n → ℝ) × (Fin n → ℝ))) | P ∈ Set.range Pk} := by
    apply IsTightMeasureSet.prodMk
    · refine (tight_of μkP μP tμ).subset ?_
      rintro _ ⟨_, ⟨_, ⟨k, rfl⟩, rfl⟩, rfl⟩
      exact ⟨μkP k, ⟨k, rfl⟩, rfl⟩
    · refine (tight_of (fun _ => νP) νP tendsto_const_nhds).subset ?_
      rintro _ ⟨_, ⟨_, ⟨k, rfl⟩, rfl⟩, rfl⟩
      exact ⟨νP, ⟨k, rfl⟩, (hπ k).2.symm⟩
  have hK := isCompact_closure_of_isTightMeasureSet tightπ
  obtain ⟨π0, -, hπ0⟩ := hK.exists_clusterPt (f := map Pk atTop)
    (by rw [le_principal_iff]; exact mem_map.2 (Eventually.of_forall fun k => subset_closure ⟨k, rfl⟩))
  have hNe : (𝓝 π0 ⊓ map Pk atTop).NeBot := hπ0
  have hLid : Tendsto (fun P => P) (𝓝 π0 ⊓ map Pk atTop) (𝓝 π0) :=
    tendsto_id.mono_left inf_le_left
  have m1 : π0.map measurable_fst.aemeasurable = μP := by
    refine tendsto_nhds_unique
      ((ProbabilityMeasure.continuous_map continuous_fst).continuousAt.tendsto.comp hLid) ?_
    refine (tendsto_map'_iff.2 ?_).mono_left inf_le_right
    convert tμ using 1
    funext k
    apply Subtype.ext
    first | rfl | simp [μkP, Pk, ProbabilityMeasure.toMeasure_map]
  have m2 : π0.map measurable_snd.aemeasurable = νP := by
    refine tendsto_nhds_unique
      ((ProbabilityMeasure.continuous_map continuous_snd).continuousAt.tendsto.comp hLid) ?_
    refine (tendsto_map'_iff.2 ?_).mono_left inf_le_right
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => νP) atTop (𝓝 νP)) using 1
    funext k
    apply Subtype.ext
    exact (hπ k).2
  refine ⟨(π0 : Measure _), inferInstance, ?_, ?_, fun F c hc => ?_⟩
  · have := congrArg (fun P : ProbabilityMeasure (Fin n → ℝ) => (P : Measure (Fin n → ℝ))) m1
    simp only [ProbabilityMeasure.toMeasure_map] at this
    exact this
  · have := congrArg (fun P : ProbabilityMeasure (Fin n → ℝ) => (P : Measure (Fin n → ℝ))) m2
    simp only [ProbabilityMeasure.toMeasure_map] at this
    exact this
  · have hT := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hLid F
    have hev : ∀ᶠ P in 𝓝 π0 ⊓ map Pk atTop,
        |∫ p, F p ∂((P : ProbabilityMeasure ((Fin n → ℝ) × (Fin n → ℝ))) : Measure _)| ≤ c :=
      Filter.mem_inf_of_right (mem_map.2 (Eventually.of_forall fun k => hc k))
    exact le_of_tendsto ((continuous_abs.tendsto _).comp hT) hev

theorem cx8_clamp_le (v u R : ℝ) (hR : 0 ≤ R) :
    |(v - u) - max (-R) (min R (v - u))| ≤ max (|v| - R / 2) 0 + max (|u| - R / 2) 0 := by
  have h1 : |(v - u) - max (-R) (min R (v - u))| ≤ max (|v - u| - R) 0 := by
    rcases le_total (v - u) (-R) with h | h
    · have : max (-R) (min R (v - u)) = -R := by
        rw [min_eq_right (by linarith)]; exact max_eq_left h
      rw [this, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      exact le_max_of_le_left (by linarith)
    · rcases le_total (v - u) R with h' | h'
      · have : max (-R) (min R (v - u)) = v - u := by
          rw [min_eq_right h']; exact max_eq_right h
        rw [this, sub_self, abs_zero]; exact le_max_right _ _
      · have : max (-R) (min R (v - u)) = R := by
          rw [min_eq_left h']; exact max_eq_right (by linarith)
        rw [this, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        exact le_max_of_le_left (by linarith)
  refine h1.trans (max_le ?_ (add_nonneg (le_max_right _ _) (le_max_right _ _)))
  have := abs_sub v u
  linarith [le_max_left (|v| - R / 2) 0, le_max_left (|u| - R / 2) 0]

theorem cx8_tail_convex {n : ℕ} (j : Fin n) (c : ℝ) :
    ConvexOn ℝ Set.univ (fun x : Fin n → ℝ => max (|x j| - c) 0) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  have h1 : |a * x j + b * y j| ≤ a * |x j| + b * |y j| := by
    have := abs_add_le (a * x j) (b * y j)
    rwa [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] at this
  have h2 := mul_le_mul_of_nonneg_left (le_max_left (|x j| - c) 0) ha
  have h3 := mul_le_mul_of_nonneg_left (le_max_left (|y j| - c) 0) hb
  have h4 := mul_nonneg ha (le_max_right (|x j| - c) 0)
  have h5 := mul_nonneg hb (le_max_right (|y j| - c) 0)
  have h6 : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  exact max_le (by linarith) (by linarith)

theorem cx8_tail_tendsto {n : ℕ} (m : Measure (Fin n → ℝ)) (hm : Integrable id m) (j : Fin n) :
    Tendsto (fun k : ℕ => ∫ x, max (|x j| - (k : ℝ) / 2) 0 ∂m) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := m)
    (F := fun (k : ℕ) (x : Fin n → ℝ) => max (|x j| - (k : ℝ) / 2) 0) (f := fun _ => (0 : ℝ))
    (fun x => ‖x‖) (fun k => ?_) hm.norm (fun k => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_)
  · simpa using h
  · exact (by fun_prop : Continuous fun x : Fin n → ℝ => max (|x j| - (k : ℝ) / 2) 0).aestronglyMeasurable
  · have hj : |x j| ≤ ‖x‖ := (Real.norm_eq_abs (x j)) ▸ norm_le_pi_norm x j
    have hk : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith) (norm_nonneg _)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈2 * |x j|⌉₊] with k hk
    have : 2 * |x j| ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
    rw [max_eq_right (by linarith)]

/-- Truncation error for the martingale test. -/
theorem cx8_trunc {n : ℕ} (P : Measure ((Fin n → ℝ) × (Fin n → ℝ))) [IsProbabilityMeasure P]
    (h1 : Integrable Prod.fst P) (h2 : Integrable Prod.snd P)
    (g : BoundedContinuousFunction (Fin n → ℝ) ℝ) (j : Fin n) (R : ℝ) (hR : 0 ≤ R) :
    Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => g p.1 * (p.2 j - p.1 j)) P ∧
    |∫ p, g p.1 * (p.2 j - p.1 j) ∂P - ∫ p, g p.1 * max (-R) (min R (p.2 j - p.1 j)) ∂P| ≤
      ‖g‖ * (∫ p, max (|p.2 j| - R / 2) 0 ∂P + ∫ p, max (|p.1 j| - R / 2) 0 ∂P) := by
  have hg := g.continuous
  have hgb : ∀ x, |g x| ≤ ‖g‖ := fun x => (Real.norm_eq_abs (g x)) ▸ g.norm_coe_le_norm x
  have hj1 : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 j) P :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).integrable_comp h1
  have hj2 : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.2 j) P :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).integrable_comp h2
  have hΦ : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => g p.1 * (p.2 j - p.1 j)) P := by
    refine Integrable.mono' ((hj2.sub hj1).norm.const_mul ‖g‖)
      (by fun_prop : Continuous fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        g p.1 * (p.2 j - p.1 j)).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hgb _) (abs_nonneg _)
  have hΦR : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      g p.1 * max (-R) (min R (p.2 j - p.1 j))) P := by
    refine Integrable.mono' (integrable_const (‖g‖ * R))
      (by fun_prop : Continuous fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        g p.1 * max (-R) (min R (p.2 j - p.1 j))).aestronglyMeasurable
        (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (hgb _) (abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩)
      (abs_nonneg _) (norm_nonneg _)
  have hψ : ∀ (f : (Fin n → ℝ) × (Fin n → ℝ) → ℝ), Integrable f P → Continuous f →
      Integrable (fun p => max (|f p| - R / 2) 0) P := by
    intro f hf hfc
    refine Integrable.mono' hf.norm (by fun_prop : Continuous fun p =>
      max (|f p| - R / 2) 0).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
    exact max_le (by linarith) (abs_nonneg _)
  have hψ2 := hψ (fun p => p.2 j) hj2 (by fun_prop)
  have hψ1 := hψ (fun p => p.1 j) hj1 (by fun_prop)
  refine ⟨hΦ, ?_⟩
  rw [← integral_sub hΦ hΦR, ← integral_add hψ2 hψ1, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono (hΦ.sub hΦR).abs
    ((hψ2.add hψ1).const_mul _) fun p => ?_)
  simp only
  rw [← mul_sub, abs_mul]
  exact mul_le_mul (hgb _) (cx8_clamp_le _ _ R hR) (abs_nonneg _) (norm_nonneg _)

theorem cx8_tail_int {X : Type*} [MeasurableSpace X] (P : Measure X) (f : X → ℝ)
    (hf : Integrable f P) (c : ℝ) (hc : 0 ≤ c) : Integrable (fun p => max (|f p| - c) 0) P := by
  refine Integrable.mono' hf.norm ((by fun_prop : Continuous fun t : ℝ => max (|t| - c) 0
    ).comp_aestronglyMeasurable hf.aestronglyMeasurable) (Eventually.of_forall fun p => ?_)
  try simp only [Function.comp]
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
  exact max_le (by linarith) (abs_nonneg _)

/-- The tail functional `∫ (|x_j| - R/2)⁺`. -/
noncomputable def tail8 {n : ℕ} (m : Measure (Fin n → ℝ)) (j : Fin n) (R : ℝ) : ℝ :=
  ∫ x, max (|x j| - R / 2) 0 ∂m

theorem cx8_tail_map {n : ℕ} (P : Measure ((Fin n → ℝ) × (Fin n → ℝ)))
    (f : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)) (hf : Measurable f) (j : Fin n) (R : ℝ) :
    ∫ p, max (|f p j| - R / 2) 0 ∂P = tail8 (P.map f) j R :=
  (integral_map hf.aemeasurable (by fun_prop : Continuous fun x : Fin n → ℝ =>
    max (|x j| - R / 2) 0).aestronglyMeasurable).symm

/-- The martingale tests pass to the cluster point. -/
theorem cx8_mart_limit {n : ℕ} (α β : Measure (Fin n → ℝ)) [IsProbabilityMeasure α]
    [IsProbabilityMeasure β] (hα : Integrable id α) (hβ : Integrable id β)
    (πk : ℕ → Measure ((Fin n → ℝ) × (Fin n → ℝ)))
    (hπ : ∀ k, IsProbabilityMeasure (πk k) ∧ MartPlan8 (πk k) ∧ (πk k).map Prod.snd = β ∧
      ∀ g : (Fin n → ℝ) → ℝ, Measurable g → (∃ C, ∀ x, |g x| ≤ C) → ∀ j : Fin n,
        ∫ p, g p.1 * (p.2 j - p.1 j) ∂(πk k) = 0)
    (π : Measure ((Fin n → ℝ) × (Fin n → ℝ))) [IsProbabilityMeasure π]
    (h1 : π.map Prod.fst = α) (h2 : π.map Prod.snd = β)
    (hcl : ∀ (F : BoundedContinuousFunction ((Fin n → ℝ) × (Fin n → ℝ)) ℝ) (c : ℝ),
        (∀ k, |∫ p, F p ∂(πk k)| ≤ c) → |∫ p, F p ∂π| ≤ c) :
    Integrable Prod.fst π ∧ Integrable Prod.snd π ∧
    ∀ g : BoundedContinuousFunction (Fin n → ℝ) ℝ, ∀ j : Fin n,
      ∫ p, g p.1 * (p.2 j - p.1 j) ∂π = 0 := by
  have hfst : Integrable Prod.fst π := by
    rw [← h1] at hα
    exact (integrable_map_measure measurable_id.aestronglyMeasurable
      measurable_fst.aemeasurable).1 hα
  have hsnd : Integrable Prod.snd π := by
    rw [← h2] at hβ
    exact (integrable_map_measure measurable_id.aestronglyMeasurable
      measurable_snd.aemeasurable).1 hβ
  refine ⟨hfst, hsnd, fun g j => ?_⟩
  have hgb : ∀ x, |g x| ≤ ‖g‖ := fun x => (Real.norm_eq_abs (g x)) ▸ g.norm_coe_le_norm x
  have key : ∀ R : ℝ, 0 ≤ R →
      |∫ p, g p.1 * (p.2 j - p.1 j) ∂π| ≤ ‖g‖ * (3 * tail8 β j R + tail8 α j R) := by
    intro R hR
    let FR : BoundedContinuousFunction ((Fin n → ℝ) × (Fin n → ℝ)) ℝ :=
      BoundedContinuousFunction.ofNormedAddCommGroup
        (fun p => g p.1 * max (-R) (min R (p.2 j - p.1 j)))
        (by have := g.continuous; fun_prop) (‖g‖ * R) (fun p => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hgb _) (abs_le.2 ⟨le_max_left _ _, max_le (by linarith)
            (min_le_left _ _)⟩) (abs_nonneg _) (norm_nonneg _))
    have hk : ∀ k, |∫ p, FR p ∂(πk k)| ≤ ‖g‖ * (2 * tail8 β j R) := by
      intro k
      obtain ⟨hp, hm, hs, hb⟩ := hπ k
      have hz := hb g g.continuous.measurable ⟨‖g‖, hgb⟩ j
      have ht := (cx8_trunc (πk k) hm.1 hm.2.1 g j R hR).2
      rw [hz, zero_sub, abs_neg] at ht
      have hj1 : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 j) (πk k) :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).integrable_comp hm.1
      have hj2 : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.2 j) (πk k) :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).integrable_comp hm.2.1
      have hJ := cx8_jensen (πk k) hm (fun x => max (|x j| - R / 2) 0)
        (cx8_tail_convex j (R / 2)) (cx8_tail_int _ _ hj1 _ (by linarith))
        (cx8_tail_int _ _ hj2 _ (by linarith))
      have e2 : ∫ p, max (|p.2 j| - R / 2) 0 ∂(πk k) = tail8 β j R := by
        rw [cx8_tail_map (πk k) Prod.snd measurable_snd j R, hs]
      have hFR : ∫ p, FR p ∂(πk k) =
          ∫ p, g p.1 * max (-R) (min R (p.2 j - p.1 j)) ∂(πk k) := rfl
      rw [hFR]
      refine ht.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      have : ∫ p, max (|p.1 j| - R / 2) 0 ∂(πk k) ≤ ∫ p, max (|p.2 j| - R / 2) 0 ∂(πk k) := hJ
      linarith
    have h0 := hcl FR _ hk
    have ht0 := (cx8_trunc π hfst hsnd g j R hR).2
    rw [cx8_tail_map π Prod.snd measurable_snd j R, h2,
      cx8_tail_map π Prod.fst measurable_fst j R, h1] at ht0
    have hFR : ∫ p, FR p ∂π = ∫ p, g p.1 * max (-R) (min R (p.2 j - p.1 j)) ∂π := rfl
    rw [hFR] at h0
    have := abs_sub_abs_le_abs_sub (∫ p, g p.1 * (p.2 j - p.1 j) ∂π)
      (∫ p, g p.1 * max (-R) (min R (p.2 j - p.1 j)) ∂π)
    nlinarith [norm_nonneg g]
  have hlim : Tendsto (fun k : ℕ => ‖g‖ * (3 * tail8 β j k + tail8 α j k)) atTop
      (𝓝 (‖g‖ * (3 * 0 + 0))) :=
    tendsto_const_nhds.mul (((cx8_tail_tendsto β hβ j).const_mul 3).add
      (cx8_tail_tendsto α hα j))
  have hle : |∫ p, g p.1 * (p.2 j - p.1 j) ∂π| ≤ 0 := by
    have := ge_of_tendsto hlim (Eventually.of_forall fun k => key k (Nat.cast_nonneg k))
    simpa using this
  exact abs_nonpos_iff.1 hle

/-- Bounded continuous martingale tests give the set-integral martingale property. -/
theorem cx8_set_of_bcf {n : ℕ} (π : Measure ((Fin n → ℝ) × (Fin n → ℝ)))
    [IsProbabilityMeasure π] (h1 : Integrable Prod.fst π) (h2 : Integrable Prod.snd π)
    (h : ∀ g : BoundedContinuousFunction (Fin n → ℝ) ℝ, ∀ j : Fin n,
      ∫ p, g p.1 * (p.2 j - p.1 j) ∂π = 0) : MartPlan8 π := by
  refine ⟨h1, h2, fun B hB => ?_⟩
  have hBm : MeasurableSet (Prod.fst ⁻¹' B : Set ((Fin n → ℝ) × (Fin n → ℝ))) :=
    measurable_fst hB
  have hj1 : ∀ j : Fin n, Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 j) π := fun j =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).integrable_comp h1
  have hj2 : ∀ j : Fin n, Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.2 j) π := fun j =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).integrable_comp h2
  have hcomp : ∀ j : Fin n, ∫ p in Prod.fst ⁻¹' B, (p.2 j - p.1 j) ∂π = 0 := by
    intro j
    let D : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p => p.2 j - p.1 j
    have hDi : Integrable D π := (hj2 j).sub (hj1 j)
    have hDm : Measurable D := by fun_prop
    let wP : (Fin n → ℝ) × (Fin n → ℝ) → NNReal := fun p => (D p).toNNReal
    let wN : (Fin n → ℝ) × (Fin n → ℝ) → NNReal := fun p => (-D p).toNNReal
    have hwP : Measurable wP := hDm.real_toNNReal
    have hwN : Measurable wN := hDm.neg.real_toNNReal
    have : IsFiniteMeasure (π.withDensity fun p => (wP p : ENNReal)) :=
      isFiniteMeasure_withDensity_ofReal hDi.hasFiniteIntegral
    have : IsFiniteMeasure (π.withDensity fun p => (wN p : ENNReal)) :=
      isFiniteMeasure_withDensity_ofReal hDi.neg.hasFiniteIntegral
    have hform : ∀ (w : (Fin n → ℝ) × (Fin n → ℝ) → NNReal), Measurable w →
        ∀ f : (Fin n → ℝ) → ℝ, Measurable f →
        ∫ x, f x ∂((π.withDensity fun p => (w p : ENNReal)).map Prod.fst) =
          ∫ p, (w p : ℝ) * f p.1 ∂π := by
      intro w hw f hf
      rw [integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable,
        integral_withDensity_eq_integral_smul hw]
      rfl
    have hint : ∀ (w : (Fin n → ℝ) × (Fin n → ℝ) → NNReal), Measurable w →
        (∀ p, (w p : ℝ) ≤ |D p|) → ∀ f : (Fin n → ℝ) → ℝ, Measurable f →
        (∀ x, |f x| ≤ 1) → Integrable (fun p => (w p : ℝ) * f p.1) π := by
      intro w hw hwle f hf hfb
      refine Integrable.mono' (hDi.abs.mul_const 1)
        ((hw.coe_nnreal_real.mul (hf.comp measurable_fst)).aestronglyMeasurable)
        (Eventually.of_forall fun p => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (NNReal.coe_nonneg _)]
      exact mul_le_mul (hwle p) (hfb _) (abs_nonneg _) (abs_nonneg _)
    have hPle : ∀ p, (wP p : ℝ) ≤ |D p| := fun p => by
      simp only [wP, Real.coe_toNNReal']
      exact max_le (le_abs_self _) (abs_nonneg _)
    have hNle : ∀ p, (wN p : ℝ) ≤ |D p| := fun p => by
      simp only [wN, Real.coe_toNNReal']
      exact max_le (neg_le_abs _) (abs_nonneg _)
    have hdiff : ∀ p, (wP p : ℝ) - (wN p : ℝ) = D p := fun p => by
      simp only [wP, wN, Real.coe_toNNReal']
      rcases le_total 0 (D p) with hd | hd
      · rw [max_eq_left hd, max_eq_right (by linarith)]; ring
      · rw [max_eq_right hd, max_eq_left (by linarith)]; ring
    have heq : (π.withDensity fun p => (wP p : ENNReal)).map Prod.fst =
        (π.withDensity fun p => (wN p : ENNReal)).map Prod.fst := by
      apply ext_of_forall_integral_eq_of_IsFiniteMeasure
      intro f
      have hf1 : ∀ x, |f x / (‖f‖ + 1)| ≤ 1 := fun x => by
        rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < ‖f‖ + 1), div_le_one (by positivity)]
        have := (Real.norm_eq_abs (f x)) ▸ f.norm_coe_le_norm x
        linarith
      have hfm : Measurable fun x => f x / (‖f‖ + 1) := f.continuous.measurable.div_const _
      have hz := h f j
      rw [hform wP hwP f f.continuous.measurable, hform wN hwN f f.continuous.measurable]
      have iP := (hint wP hwP hPle _ hfm hf1).mul_const (‖f‖ + 1)
      have iN := (hint wN hwN hNle _ hfm hf1).mul_const (‖f‖ + 1)
      have eP : (fun p => (wP p : ℝ) * (f p.1 / (‖f‖ + 1)) * (‖f‖ + 1)) =
          fun p => (wP p : ℝ) * f p.1 := by
        funext p; field_simp
      have eN : (fun p => (wN p : ℝ) * (f p.1 / (‖f‖ + 1)) * (‖f‖ + 1)) =
          fun p => (wN p : ℝ) * f p.1 := by
        funext p; field_simp
      rw [eP] at iP
      rw [eN] at iN
      rw [← sub_eq_zero, ← integral_sub iP iN, ← hz]
      congr 1; funext p
      rw [← sub_mul, hdiff]; ring
    have hind : Measurable (B.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hB
    have hindb : ∀ x, |B.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := fun x => by
      by_cases hx : x ∈ B <;> simp [Set.indicator, hx]
    have := congrArg (fun ν => ∫ x, B.indicator (fun _ => (1 : ℝ)) x ∂ν) heq
    try simp only at this
    rw [hform wP hwP _ hind, hform wN hwN _ hind] at this
    rw [← integral_indicator hBm]
    have e : (Prod.fst ⁻¹' B).indicator (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.2 j - p.1 j) =
        fun p => (wP p : ℝ) * B.indicator (fun _ => (1 : ℝ)) p.1 -
          (wN p : ℝ) * B.indicator (fun _ => (1 : ℝ)) p.1 := by
      funext p
      by_cases hp : p.1 ∈ B
      · simp only [Set.indicator, Set.mem_preimage, hp, if_true, mul_one]
        exact (hdiff p).symm
      · simp [Set.indicator, hp]
    rw [e, integral_sub (hint wP hwP hPle _ hind hindb) (hint wN hwN hNle _ hind hindb), this,
      sub_self]
  funext j
  have a := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).integral_comp_comm
    (h2.integrableOn (s := Prod.fst ⁻¹' B))
  have b := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).integral_comp_comm
    (h1.integrableOn (s := Prod.fst ⁻¹' B))
  simp only [ContinuousLinearMap.proj_apply] at a b
  rw [← a, ← b]
  have := hcomp j
  rw [integral_sub (hj2 j).integrableOn (hj1 j).integrableOn] at this
  linarith

/-- Cell-mean discretization along a finite measurable partition. -/
theorem cx8_cells {n m : ℕ} (α : Measure (Fin n → ℝ)) [IsProbabilityMeasure α]
    (hα : Integrable id α) (G : (Fin n → ℝ) → Fin m) (hG : Measurable G) :
    (∀ φ, CxTest8 φ →
      ∑ i, α.real (G ⁻¹' {i}) * φ (⨍ x in G ⁻¹' {i}, x ∂α) ≤ ∫ x, φ x ∂α) ∧
    (∀ g : (Fin n → ℝ) → ℝ, Measurable g → (∃ C, ∀ x, |g x| ≤ C) →
      ∫ x, g (⨍ y in G ⁻¹' {G x}, y ∂α) ∂α =
        ∑ i, α.real (G ⁻¹' {i}) * g (⨍ x in G ⁻¹' {i}, x ∂α)) := by
  classical
  have hc : ∀ i, MeasurableSet (G ⁻¹' {i}) := fun i => hG (measurableSet_singleton i)
  have hdec : ∀ f : (Fin n → ℝ) → ℝ, Integrable f α →
      ∫ x, f x ∂α = ∑ i, ∫ x in G ⁻¹' {i}, f x ∂α := by
    intro f hf
    have e : (fun x => f x) = fun x => ∑ i, (G ⁻¹' {i}).indicator f x := by
      funext x
      rw [Finset.sum_eq_single (G x)]
      · simp [Set.indicator]
      · intro b _ hb
        have : x ∉ G ⁻¹' {b} := fun h => hb (Set.mem_singleton_iff.1 h).symm
        simp [Set.indicator_of_notMem this]
      · intro h; exact absurd (Finset.mem_univ _) h
    calc ∫ x, f x ∂α = ∫ x, ∑ i, (G ⁻¹' {i}).indicator f x ∂α :=
          congrArg (fun h => ∫ x, h x ∂α) e
      _ = ∑ i, ∫ x, (G ⁻¹' {i}).indicator f x ∂α :=
          integral_finset_sum _ (fun i _ => hf.indicator (hc i))
      _ = ∑ i, ∫ x in G ⁻¹' {i}, f x ∂α :=
          Finset.sum_congr rfl fun i _ => integral_indicator (hc i)
  constructor
  · intro φ hφ
    have hφi := cx8_test_int α hα φ hφ
    rw [hdec φ hφi]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases h0 : α (G ⁻¹' {i}) = 0
    · have : α.real (G ⁻¹' {i}) = 0 := by simp [Measure.real, h0]
      rw [this, zero_mul, setIntegral_measure_zero _ h0]
    · have hJ := hφ.1.map_set_average_le (f := fun x => x) (cx8_cont hφ.1).continuousOn
        isClosed_univ h0 (measure_ne_top _ _) (Eventually.of_forall fun _ => Set.mem_univ _)
        hα.integrableOn hφi.integrableOn
      rw [setAverage_eq α φ (G ⁻¹' {i}), smul_eq_mul] at hJ
      have hp : 0 < α.real (G ⁻¹' {i}) := ENNReal.toReal_pos h0 (measure_ne_top _ _)
      calc α.real (G ⁻¹' {i}) * φ (⨍ x in G ⁻¹' {i}, x ∂α)
          ≤ α.real (G ⁻¹' {i}) * ((α.real (G ⁻¹' {i}))⁻¹ * ∫ x in G ⁻¹' {i}, φ x ∂α) :=
            mul_le_mul_of_nonneg_left hJ hp.le
        _ = ∫ x in G ⁻¹' {i}, φ x ∂α := by rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
  · intro g hg ⟨C, hC⟩
    have hgm : Measurable fun x => g (⨍ y in G ⁻¹' {G x}, y ∂α) :=
      hg.comp ((measurable_of_finite (fun i : Fin m => ⨍ y in G ⁻¹' {i}, y ∂α)).comp hG)
    have hgi : Integrable (fun x => g (⨍ y in G ⁻¹' {G x}, y ∂α)) α :=
      Integrable.mono' (integrable_const C) hgm.aestronglyMeasurable
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC _)
    rw [hdec _ hgi]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [setIntegral_congr_fun (hc i) (g := fun _ => g (⨍ x in G ⁻¹' {i}, x ∂α))
      (fun x hx => by
        have : G x = i := Set.mem_singleton_iff.1 hx
        simp only [this]), setIntegral_const, smul_eq_mul]

/-- Clamped integer grid of mesh `1/(k+1)`. -/
noncomputable def gridZ8 {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : Fin n → ℤ :=
  fun i => max (-(((k : ℤ) + 1) ^ 2)) (min (((k : ℤ) + 1) ^ 2) ⌊((k : ℝ) + 1) * x i⌋)

noncomputable def gridS8 (n k : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(((k : ℤ) + 1) ^ 2)) (((k : ℤ) + 1) ^ 2)

theorem gridZ8_mem {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : gridZ8 k x ∈ gridS8 n k := by
  simp only [gridS8, Fintype.mem_piFinset, Finset.mem_Icc, gridZ8]
  intro i
  have h0 : (0 : ℤ) ≤ ((k : ℤ) + 1) ^ 2 := by positivity
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem gridZ8_meas {n : ℕ} (k : ℕ) : Measurable (gridZ8 (n := n) k) := by
  refine measurable_pi_lambda _ fun i => ?_
  exact (measurable_of_countable (fun z : ℤ =>
    max (-(((k : ℤ) + 1) ^ 2)) (min (((k : ℤ) + 1) ^ 2) z))).comp
    (Int.measurable_floor.comp ((measurable_pi_apply i).const_mul _))

noncomputable def gridG8 (n k : ℕ) (x : Fin n → ℝ) : Fin (gridS8 n k).card :=
  (gridS8 n k).equivFin ⟨gridZ8 k x, gridZ8_mem k x⟩

theorem gridG8_eq {n k : ℕ} (x y : Fin n → ℝ) (h : gridG8 n k y = gridG8 n k x) :
    gridZ8 k y = gridZ8 k x := by
  have := (gridS8 n k).equivFin.injective h
  exact congrArg Subtype.val this

theorem gridG8_meas (n k : ℕ) : Measurable (gridG8 n k) := by
  refine measurable_to_countable' fun i => ?_
  have : gridG8 n k ⁻¹' {i} = gridZ8 k ⁻¹' {((gridS8 n k).equivFin.symm i).1} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, gridG8]
    rw [Equiv.apply_eq_iff_eq_symm_apply]
    exact ⟨fun h => by rw [← h], fun h => Subtype.ext h⟩
  rw [this]
  exact gridZ8_meas k (measurableSet_singleton _)

theorem gridS8_pos (n k : ℕ) : 0 < (gridS8 n k).card :=
  Finset.card_pos.2 ⟨_, gridZ8_mem k (0 : Fin n → ℝ)⟩

theorem gridZ8_close {n : ℕ} (k : ℕ) (x y : Fin n → ℝ) (hk : ‖x‖ + 1 ≤ (k : ℝ))
    (h : gridZ8 k y = gridZ8 k x) : dist y x ≤ 1 / ((k : ℝ) + 1) := by
  have hkp : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
  have hi := congrFun h i
  simp only [gridZ8] at hi
  have hxi : |x i| ≤ ‖x‖ := (Real.norm_eq_abs (x i)) ▸ norm_le_pi_norm x i
  have hx1 : ((⌊((k : ℝ) + 1) * x i⌋ : ℤ) : ℝ) ≤ ((k : ℝ) + 1) * x i := Int.floor_le _
  have hx2 : ((k : ℝ) + 1) * x i < ((⌊((k : ℝ) + 1) * x i⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hy1 : ((⌊((k : ℝ) + 1) * y i⌋ : ℤ) : ℝ) ≤ ((k : ℝ) + 1) * y i := Int.floor_le _
  have hy2 : ((k : ℝ) + 1) * y i < ((⌊((k : ℝ) + 1) * y i⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hab := abs_le.1 hxi
  have hb1 : ((k : ℝ) + 1) * x i ≤ ((k : ℝ) + 1) * ‖x‖ :=
    mul_le_mul_of_nonneg_left hab.2 hkp.le
  have hb2 : -(((k : ℝ) + 1) * ‖x‖) ≤ ((k : ℝ) + 1) * x i := by nlinarith
  have hnx : 0 ≤ ‖x‖ := norm_nonneg x
  have hlt : ((⌊((k : ℝ) + 1) * x i⌋ : ℤ) : ℝ) < (((((k : ℤ) + 1) ^ 2 : ℤ)) : ℝ) := by
    push_cast; nlinarith
  have hgt : -((((((k : ℤ) + 1) ^ 2 : ℤ)) : ℝ)) < ((⌊((k : ℝ) + 1) * x i⌋ : ℤ) : ℝ) := by
    push_cast; nlinarith
  have hlt' : ⌊((k : ℝ) + 1) * x i⌋ < ((k : ℤ) + 1) ^ 2 := by exact_mod_cast hlt
  have hgt' : -(((k : ℤ) + 1) ^ 2) < ⌊((k : ℝ) + 1) * x i⌋ := by exact_mod_cast hgt
  have heq : ⌊((k : ℝ) + 1) * y i⌋ = ⌊((k : ℝ) + 1) * x i⌋ := by
    generalize ((k : ℤ) + 1) ^ 2 = M at hi hlt' hgt'
    generalize ⌊((k : ℝ) + 1) * y i⌋ = a at hi ⊢
    generalize ⌊((k : ℝ) + 1) * x i⌋ = b at hi hlt' hgt' ⊢
    simp only [max_def, min_def] at hi
    split_ifs at hi <;> omega
  rw [heq] at hy1 hy2
  rw [Real.dist_eq, le_div_iff₀ hkp]
  have h3 : |((k : ℝ) + 1) * (y i - x i)| < 1 := abs_lt.2 ⟨by nlinarith, by nlinarith⟩
  rw [abs_mul, abs_of_pos hkp] at h3
  linarith

/-- The cell means converge to the point, almost everywhere. -/
theorem cx8_grid_conv {n : ℕ} (α : Measure (Fin n → ℝ)) [IsProbabilityMeasure α]
    (hα : Integrable id α) :
    ∀ᵐ x ∂α, Tendsto (fun k => ⨍ y in gridG8 n k ⁻¹' {gridG8 n k x}, y ∂α) atTop (𝓝 x) := by
  have hpos : ∀ᵐ x ∂α, ∀ k, α (gridG8 n k ⁻¹' {gridG8 n k x}) ≠ 0 := by
    rw [ae_all_iff]
    intro k
    have : ∀ i, ∀ᵐ x ∂α, gridG8 n k x = i → α (gridG8 n k ⁻¹' {i}) ≠ 0 := by
      intro i
      by_cases h : α (gridG8 n k ⁻¹' {i}) = 0
      · refine ae_iff.2 (measure_mono_null (fun x hx => ?_) h)
        simp only [Set.mem_setOf_eq, _root_.not_imp] at hx
        exact hx.1
      · exact Eventually.of_forall fun x _ => h
    filter_upwards [ae_all_iff.2 this] with x hx
    exact hx (gridG8 n k x) rfl
  filter_upwards [hpos] with x hx
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun k => dist_nonneg) ?_
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [eventually_ge_atTop (⌈‖x‖⌉₊ + 1)] with k hk
  have hkx : ‖x‖ + 1 ≤ (k : ℝ) := by
    have h1 : ‖x‖ ≤ (⌈‖x‖⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈‖x‖⌉₊ + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    push_cast at h2
    linarith
  have hcm : MeasurableSet (gridG8 n k ⁻¹' {gridG8 n k x}) :=
    gridG8_meas n k (measurableSet_singleton _)
  have hmem := Convex.set_average_mem (f := fun y => y) (convex_closedBall x (1 / ((k : ℝ) + 1)))
    Metric.isClosed_closedBall (hx k) (measure_ne_top _ _)
    (ae_restrict_of_forall_mem hcm fun y hy => ?_) hα.integrableOn
  · exact Metric.mem_closedBall.1 hmem
  · exact Metric.mem_closedBall.2 (gridZ8_close k x y hkx (gridG8_eq x y hy))


theorem cx8_term {n : ℕ} (f : (Fin n → ℝ) → ℝ) (L : NNReal) (hL : LipschitzWith L f) (C' : ℝ)
    (hfb : ∀ x, |f x| ≤ C') (p q ε : ℝ) (a b r : Fin n → ℝ) (hq : 0 ≤ q) (hqb : q • b = r)
    (h1 : |q - p| < ε) (h2 : ‖r - p • a‖ < ε) :
    |p * f a - q * f b| ≤ (L : ℝ) * (ε * ‖a‖ + ε) + C' * ε := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans h1.le
  have hab : q * ‖a - b‖ ≤ ε * ‖a‖ + ε := by
    have e1 : q * ‖a - b‖ = ‖q • a - r‖ := by
      rw [← hqb, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]
    have e2 : q • a - r = (q - p) • a + (p • a - r) := by rw [sub_smul]; abel
    rw [e1, e2]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, norm_sub_rev]
    exact add_le_add (mul_le_mul_of_nonneg_right h1.le (norm_nonneg a)) h2.le
  have hf : |f a - f b| ≤ L * ‖a - b‖ := by
    have := hL.dist_le_mul a b
    rwa [Real.dist_eq, dist_eq_norm] at this
  have e : p * f a - q * f b = q * (f a - f b) + (p - q) * f a := by ring
  rw [e]
  calc |q * (f a - f b) + (p - q) * f a| ≤ |q * (f a - f b)| + |(p - q) * f a| := abs_add_le _ _
    _ = q * |f a - f b| + |q - p| * |f a| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hq, abs_sub_comm p q]
    _ ≤ q * (L * ‖a - b‖) + ε * C' :=
        add_le_add (mul_le_mul_of_nonneg_left hf hq)
          (mul_le_mul h1.le (hfb a) (abs_nonneg _) hε)
    _ = L * (q * ‖a - b‖) + ε * C' := by ring
    _ ≤ L * (ε * ‖a‖ + ε) + ε * C' :=
        add_le_add (mul_le_mul_of_nonneg_left hab L.2) le_rfl
    _ = (L : ℝ) * (ε * ‖a‖ + ε) + C' * ε := by ring

/-- Strassen's theorem for laws on `ℝⁿ`: discretize, semi-discrete selections, limit. -/
theorem cx8_strassen {n : ℕ} (α β : Measure (Fin n → ℝ)) [IsProbabilityMeasure α]
    [IsProbabilityMeasure β] (hα : Integrable id α) (hβ : Integrable id β)
    (hord : ∀ φ, CxTest8 φ → ∫ x, φ x ∂α ≤ ∫ y, φ y ∂β) :
    ∃ π : Measure ((Fin n → ℝ) × (Fin n → ℝ)), IsProbabilityMeasure π ∧ MartPlan8 π ∧
      π.map Prod.fst = α ∧ π.map Prod.snd = β := by
  classical
  let G : ∀ k, (Fin n → ℝ) → Fin (gridS8 n k).card := fun k => gridG8 n k
  let p : ∀ k, Fin (gridS8 n k).card → ℝ := fun k i => α.real (G k ⁻¹' {i})
  let a : ∀ k, Fin (gridS8 n k).card → (Fin n → ℝ) := fun k i => ⨍ x in G k ⁻¹' {i}, x ∂α
  have hcells := fun k => cx8_cells α hα (G k) (gridG8_meas n k)
  let A : ℕ → ℝ := fun k => ((gridS8 n k).card : ℝ) + ∑ i, ‖a k i‖
  have hS : ∀ k, 0 ≤ ∑ i, ‖a k i‖ := fun k => Finset.sum_nonneg fun i _ => norm_nonneg _
  have hm1 : ∀ k, (1 : ℝ) ≤ ((gridS8 n k).card : ℝ) := fun k => by
    exact_mod_cast gridS8_pos n k
  have hA : ∀ k, 1 ≤ A k := fun k => by
    have := hS k
    have := hm1 k
    simp only [A]; linarith
  let ε : ℕ → ℝ := fun k => 1 / (((k : ℝ) + 1) * A k)
  have hε : ∀ k, 0 < ε k := fun k => by
    have := hA k
    simp only [ε]; positivity
  have hεA : ∀ k, ε k * A k = 1 / ((k : ℝ) + 1) := fun k => by
    have := hA k
    simp only [ε]; field_simp
  have hsel : ∀ k, ∃ θ : Fin (gridS8 n k).card → (Fin n → ℝ) → ℝ, (∀ l, Measurable (θ l)) ∧
      (∀ l y, 0 ≤ θ l y) ∧ (∀ y, ∑ l, θ l y = 1) ∧
      ∀ l, |∫ y, θ l y ∂β - p k l| < ε k ∧ ‖∫ y, θ l y • y ∂β - p k l • a k l‖ < ε k :=
    fun k => cx8_semidiscrete (gridS8_pos n k) β hβ (p k) (a k) (fun i => measureReal_nonneg)
      (fun φ hφ => ((hcells k).1 φ hφ).trans (hord φ hφ)) (ε k) (hε k)
  choose θ hθm hθ0 hθ1 hθε using hsel
  have hplan := fun k => cx8_plan β hβ (θ k) (hθm k) (hθ0 k) (hθ1 k)
  choose πk hπ using hplan
  have hbex : ∀ k, ∃ b : Fin (gridS8 n k).card → (Fin n → ℝ),
      (∀ l, (∫ y, θ k l y ∂β) • b l = ∫ y, θ k l y • y ∂β) ∧
      ∀ g : (Fin n → ℝ) → ℝ, Measurable g → (∃ C, ∀ x, |g x| ≤ C) →
        ∫ p, g p.1 ∂(πk k) = ∑ l, (∫ y, θ k l y ∂β) * g (b l) :=
    fun k => (hπ k).2.2.2.2
  choose b hb hπg using hbex
  have hPk : ∀ k, IsProbabilityMeasure ((πk k).map Prod.fst) := fun k => by
    have := (hπ k).1
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  let Pk : ℕ → ProbabilityMeasure (Fin n → ℝ) := fun k => ⟨(πk k).map Prod.fst, hPk k⟩
  let αP : ProbabilityMeasure (Fin n → ℝ) := ⟨α, inferInstance⟩
  have hgrid := cx8_grid_conv α hα
  have hT : Tendsto Pk atTop (𝓝 αP) := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    intro f ⟨C, hC⟩ ⟨L, hL⟩
    have hfc : Continuous f := hL.continuous
    have hfb : ∀ x, |f x| ≤ |f 0| + C := fun x => by
      have h1 := hC x 0
      rw [Real.dist_eq] at h1
      have h2 := abs_sub_abs_le_abs_sub (f x) (f 0)
      linarith
    have hC0 : 0 ≤ |f 0| + C := (abs_nonneg _).trans (hfb 0)
    have e1 : ∀ k, ∫ x, f x ∂((Pk k : ProbabilityMeasure (Fin n → ℝ)) : Measure (Fin n → ℝ)) =
        ∑ l, (∫ y, θ k l y ∂β) * f (b k l) := fun k => by
      show ∫ x, f x ∂((πk k).map Prod.fst) = _
      rw [integral_map measurable_fst.aemeasurable hfc.aestronglyMeasurable]
      exact hπg k f hfc.measurable ⟨_, hfb⟩
    have e2 : (fun k => ∑ l, p k l * f (a k l)) =
        fun k => ∫ x, f (⨍ y in G k ⁻¹' {G k x}, y ∂α) ∂α :=
      funext fun k => ((hcells k).2 f hfc.measurable ⟨_, hfb⟩).symm
    have t2 : Tendsto (fun k => ∑ l, p k l * f (a k l)) atTop (𝓝 (∫ x, f x ∂α)) := by
      rw [e2]
      exact tendsto_integral_of_dominated_convergence (fun _ => |f 0| + C)
        (fun k => (hfc.measurable.comp ((measurable_of_finite
          (fun i : Fin (gridS8 n k).card => ⨍ y in G k ⁻¹' {i}, y ∂α)).comp
          (gridG8_meas n k))).aestronglyMeasurable)
        (integrable_const _) (fun k => Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact hfb _)
        (hgrid.mono fun x hx => (hfc.tendsto x).comp hx)
    have hd : ∀ k, dist (∑ l, p k l * f (a k l)) (∑ l, (∫ y, θ k l y ∂β) * f (b k l)) ≤
        ((L : ℝ) + (|f 0| + C)) * (1 / ((k : ℝ) + 1)) := by
      intro k
      rw [Real.dist_eq, ← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun l _ => cx8_term f L hL _ hfb (p k l) (∫ y, θ k l y ∂β)
        (ε k) (a k l) (b k l) (∫ y, θ k l y • y ∂β) (integral_nonneg (hθ0 k l)) (hb k l)
        (hθε k l).1 (hθε k l).2).trans ?_
      have hL0 : (0 : ℝ) ≤ L := L.2
      have h3 := mul_nonneg (mul_nonneg (hε k).le hC0) (hS k)
      calc ∑ l, ((L : ℝ) * (ε k * ‖a k l‖ + ε k) + (|f 0| + C) * ε k)
          = ∑ l, (((L : ℝ) * ε k) * ‖a k l‖ + ((L : ℝ) * ε k + (|f 0| + C) * ε k)) :=
            Finset.sum_congr rfl fun l _ => by ring
        _ = ((L : ℝ) * ε k) * ∑ l, ‖a k l‖ +
              ((gridS8 n k).card : ℝ) * ((L : ℝ) * ε k + (|f 0| + C) * ε k) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
        _ ≤ ((L : ℝ) + (|f 0| + C)) * (ε k * A k) := by
            simp only [A]
            nlinarith
        _ = ((L : ℝ) + (|f 0| + C)) * (1 / ((k : ℝ) + 1)) := by rw [hεA k]
    refine (t2.congr_dist (squeeze_zero (fun k => dist_nonneg) hd ?_)).congr (fun k => (e1 k).symm)
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((L : ℝ) + (|f 0| + C)))
  have hconv : ∀ g : BoundedContinuousFunction (Fin n → ℝ) ℝ,
      Tendsto (fun k => ∫ p, g p.1 ∂(πk k)) atTop (𝓝 (∫ x, g x ∂α)) := by
    intro g
    have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hT g
    refine this.congr fun k => ?_
    show ∫ x, g x ∂((πk k).map Prod.fst) = _
    exact integral_map measurable_fst.aemeasurable g.continuous.aestronglyMeasurable
  obtain ⟨π, hπ1, h1, h2, hcl⟩ := cx8_cluster α β πk (fun k => ⟨(hπ k).1, (hπ k).2.2.1⟩) hconv
  obtain ⟨i1, i2, hm⟩ := cx8_mart_limit α β hα hβ πk
    (fun k => ⟨(hπ k).1, (hπ k).2.1, (hπ k).2.2.1, (hπ k).2.2.2.1⟩) π h1 h2 hcl
  exact ⟨π, hπ1, cx8_set_of_bcf π i1 i2 hm, h1, h2⟩

open StochasticOrders.MultivariateVariability MeasureTheory ProbabilityTheory in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {n : ℕ} (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hXint : Integrable X μ) (hYint : Integrable Y ν) :
    ConvexOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → Fin n → ℝ),
        Measurable Xhat ∧ Measurable Yhat ∧
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧
        ρ[Yhat | MeasurableSpace.comap Xhat inferInstance] =ᵐ[ρ] Xhat := by
  constructor
  · intro h
    have : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
    have : IsProbabilityMeasure (ν.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
    have i1 : Integrable id (μ.map X) :=
      (integrable_map_measure measurable_id.aestronglyMeasurable hX.aemeasurable).2 hXint
    have i2 : Integrable id (ν.map Y) :=
      (integrable_map_measure measurable_id.aestronglyMeasurable hY.aemeasurable).2 hYint
    obtain ⟨π, hπp, hπ, h1, h2⟩ := cx8_strassen (μ.map X) (ν.map Y) i1 i2
      (fun φ hφ => cx8_order_laws μ ν X Y hX hY hXint hYint h φ hφ)
    exact cx8_witness μ ν X Y hX hY π hπ h1 h2
  · rintro ⟨Ω'', _, ρ, _, Xh, Yh, hXm, -, hIX, hIY, hmart⟩
    exact cx8_converse μ ν X Y hYint ρ Xh Yh hXm hIX hIY hmart
