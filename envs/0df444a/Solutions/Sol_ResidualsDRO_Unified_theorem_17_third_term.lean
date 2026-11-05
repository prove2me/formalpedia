-- Prove2me | solution 1 for ResidualsDRO.Unified.theorem_17_third_term
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:30:09.16486+00:00
-- url     : https://prove2.me/submissions/eb5b983a-98a1-4881-9b9b-28d4a88aa050

import Mathlib
import Definitions.Def_ResidualsDRO_Unified_IsBigOp
import Definitions.Def_ResidualsDRO_Unified_Setting
import Definitions.Def_ResidualsDRO_Unified_Assumptions

open MeasureTheory Filter
open scoped ENNReal Topology NNReal BoundedContinuousFunction

namespace ResidualsDRO.Unified

/-- The cutoff `φ ↦ min 1 (‖φ‖ - m)⁺`, a bounded continuous `ℝ≥0`-valued function. -/
noncomputable def rdro17Cut {E : Type*} [SeminormedAddCommGroup E] (m : ℝ) : E →ᵇ ℝ≥0 :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun φ => Real.toNNReal (min 1 (‖φ‖ - m)),
      continuous_real_toNNReal.comp (continuous_const.min (continuous_norm.sub continuous_const))⟩
    1 (by
      intro a b
      simp only [ContinuousMap.coe_mk]
      rw [NNReal.dist_eq]
      have h1 : ((Real.toNNReal (min 1 (‖a‖ - m)) : ℝ)) ≤ 1 := by
        rw [Real.coe_toNNReal']; exact max_le (min_le_left _ _) zero_le_one
      have h2 : ((Real.toNNReal (min 1 (‖b‖ - m)) : ℝ)) ≤ 1 := by
        rw [Real.coe_toNNReal']; exact max_le (min_le_left _ _) zero_le_one
      have h3 := (Real.toNNReal (min 1 (‖a‖ - m))).2
      have h4 := (Real.toNNReal (min 1 (‖b‖ - m))).2
      rw [abs_le]; constructor <;> linarith)

lemma rdro17Cut_apply {E : Type*} [SeminormedAddCommGroup E] (m : ℝ) (φ : E) :
    rdro17Cut m φ = Real.toNNReal (min 1 (‖φ‖ - m)) := rfl

lemma rdro17Cut_le_one {E : Type*} [SeminormedAddCommGroup E] (m : ℝ) (φ : E) :
    rdro17Cut m φ ≤ 1 := by
  rw [rdro17Cut_apply, ← NNReal.coe_le_coe, Real.coe_toNNReal']
  exact max_le (min_le_left _ _) zero_le_one

lemma rdro17Cut_eq_zero {E : Type*} [SeminormedAddCommGroup E] (m : ℝ) (φ : E) (h : ‖φ‖ ≤ m) :
    rdro17Cut m φ = 0 := by
  rw [rdro17Cut_apply, Real.toNNReal_eq_zero]
  exact (min_le_right _ _).trans (by linarith)

lemma rdro17Cut_one {E : Type*} [SeminormedAddCommGroup E] (m : ℝ) (φ : E) (h : m + 1 ≤ ‖φ‖) :
    rdro17Cut m φ = 1 := by
  rw [rdro17Cut_apply, min_eq_left (by linarith)]; simp

lemma rdro17Cut_lt_one {E : Type*} [SeminormedAddCommGroup E] (m : ℝ) (φ : E)
    (h : (rdro17Cut m φ : ℝ≥0∞) < 1) : ‖φ‖ < m + 1 := by
  by_contra hc
  push Not at hc
  rw [rdro17Cut_one m φ hc] at h
  simp at h

end ResidualsDRO.Unified

open ResidualsDRO.Unified

theorem solution
    {dx dy dz : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ERData dx dy Ω) (x : EuclideanSpace ℝ (Fin dx))
    (Pε : Measure (EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure Pε]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (𝒵 : Set (EuclideanSpace ℝ (Fin dz))) (h𝒵 : IsCompact 𝒵) (h𝒵ne : 𝒵.Nonempty)
    (h𝒴ne : D.𝒴.Nonempty) (h𝒴closed : IsClosed D.𝒴) (h𝒴convex : Convex ℝ D.𝒴)
    (hproj : IsProjection D.𝒴 D.proj)
    (hrange : ∀ (i : ℕ) (ω : Ω), D.fstar x + D.eps i ω ∈ D.𝒴)
    (hint : ∀ z ∈ 𝒵, Integrable (fun e => c z (D.fstar x + e)) Pε)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (V : Ω' → C(𝒵, ℝ)) (h14 : Assumption14 P c D x Pε 𝒵 P' V)
    :
    IsBigOp P (fun n ω => ⨆ z ∈ 𝒵,
        ENNReal.ofReal |gstarN c D x n ω z - gTrue c D x Pε z|) (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have : CompactSpace 𝒵 := isCompact_iff_compactSpace.mp h𝒵
  obtain ⟨hcont1, hcont2, hconv⟩ := h14
  set X : ℕ → Ω → C(𝒵, ℝ) := fun n => fcltProcess c D x Pε 𝒵 n with hX
  -- pointwise identification of the process
  have hXapp : ∀ n ω (z : 𝒵), X n ω z =
      Real.sqrt n * (gstarN c D x n ω z - gTrue c D x Pε z) := by
    intro n ω z
    have hc : Continuous (fun z : 𝒵 => Real.sqrt n * (gstarN c D x n ω z - gTrue c D x Pε z)) :=
      continuous_const.mul (((hcont1 n ω).domRestrict).sub hcont2.domRestrict)
    simp only [hX, fcltProcess, dif_pos hc]
    rfl
  intro δ hδ
  -- Step 1: choose the cutoff level `m` from the limit `V`.
  have hVmeas : AEMeasurable V P' := hconv.aemeasurable_limit
  have hcutmeas : ∀ m : ℝ, Measurable (fun φ : C(𝒵, ℝ) => (rdro17Cut m φ : ℝ≥0∞)) := fun m =>
    measurable_coe_nnreal_ennreal.comp (rdro17Cut m).continuous.measurable
  have hlimV : Tendsto (fun m : ℕ => ∫⁻ ω', (rdro17Cut (m : ℝ) (V ω') : ℝ≥0∞) ∂P') atTop
      (𝓝 (∫⁻ _ω', (0 : ℝ≥0∞) ∂P')) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun _ => 1)
      (fun m => (hcutmeas m).comp_aemeasurable hVmeas)
      (fun m => ae_of_all _ fun ω' => by
        show ((rdro17Cut (m : ℝ) (V ω') : ℝ≥0) : ℝ≥0∞) ≤ 1
        exact_mod_cast rdro17Cut_le_one _ _)
      (by simp) (ae_of_all _ fun ω' => ?_)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (⌈‖V ω'‖⌉₊)] with m hm
    rw [rdro17Cut_eq_zero]
    · simp
    · exact (Nat.le_ceil _).trans (by exact_mod_cast hm)
  rw [lintegral_zero] at hlimV
  have hδ' : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
  obtain ⟨m, hm⟩ := (hlimV.eventually (gt_mem_nhds hδ')).exists
  -- Step 2: weak convergence transfers the bound to `X n` for large `n`.
  have hlimX : Tendsto (fun n => ∫⁻ ω, (rdro17Cut (m : ℝ) (X n ω) : ℝ≥0∞) ∂P) atTop
      (𝓝 (∫⁻ ω', (rdro17Cut (m : ℝ) (V ω') : ℝ≥0∞) ∂P')) := by
    have h := (ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mp hconv.tendsto)
      (rdro17Cut (m : ℝ))
    simp only [ProbabilityMeasure.coe_mk] at h
    rw [lintegral_map' (hcutmeas _).aemeasurable hVmeas] at h
    convert h using 2 with n
    rw [lintegral_map' (hcutmeas _).aemeasurable (hconv.forall_aemeasurable n)]
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlimX.eventually (gt_mem_nhds hm))
  refine ⟨(m : ℝ) + 1, by positivity, max N 1, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  -- Step 3: the event is contained in `{1 ≤ cut (X n)}`, then Markov.
  have hsub : {ω | ENNReal.ofReal (((m : ℝ) + 1) * (n : ℝ) ^ (-(1 / 2 : ℝ))) <
      ⨆ z ∈ 𝒵, ENNReal.ofReal |gstarN c D x n ω z - gTrue c D x Pε z|} ⊆
      {ω | (1 : ℝ≥0∞) ≤ (rdro17Cut (m : ℝ) (X n ω) : ℝ≥0∞)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    by_contra hlt
    push Not at hlt
    have hnorm := rdro17Cut_lt_one _ _ hlt
    refine absurd hω (not_lt.mpr (iSup₂_le fun z hz => ENNReal.ofReal_le_ofReal ?_))
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
    have hrp : (n : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt n)⁻¹ := by
      rw [Real.rpow_neg (by linarith), Real.sqrt_eq_rpow]
    have hpt : |X n ω ⟨z, hz⟩| ≤ ‖X n ω‖ := by
      have := ContinuousMap.norm_coe_le_norm (X n ω) ⟨z, hz⟩
      rwa [Real.norm_eq_abs] at this
    rw [hXapp, abs_mul, abs_of_pos hsq] at hpt
    rw [hrp, ← div_eq_mul_inv, le_div_iff₀ hsq]
    linarith
  calc P {ω | ENNReal.ofReal (((m : ℝ) + 1) * (n : ℝ) ^ (-(1 / 2 : ℝ))) <
      ⨆ z ∈ 𝒵, ENNReal.ofReal |gstarN c D x n ω z - gTrue c D x Pε z|}
      ≤ P {ω | (1 : ℝ≥0∞) ≤ (rdro17Cut (m : ℝ) (X n ω) : ℝ≥0∞)} := measure_mono hsub
    _ = 1 * P {ω | (1 : ℝ≥0∞) ≤ (rdro17Cut (m : ℝ) (X n ω) : ℝ≥0∞)} := (one_mul _).symm
    _ ≤ ∫⁻ ω, (rdro17Cut (m : ℝ) (X n ω) : ℝ≥0∞) ∂P :=
        mul_meas_ge_le_lintegral₀ ((hcutmeas _).comp_aemeasurable
          (hconv.forall_aemeasurable n)) 1
    _ ≤ ENNReal.ofReal δ := (hN n hnN).le
