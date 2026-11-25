-- Prove2me | solution 1 for PI.QuotMeasUniqW.qmuWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:11:38.877592+00:00
-- url     : https://prove2.me/submissions/1efa168b-c63a-4593-a2a0-4a2f93002735

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QmuWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QLiftIsMulLeftInvariant
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_Weight
import Theorems.Thm_PI_QuotMeasUniqW_hAvg_indicator_le
import Theorems.Thm_PI_QuotMeasUniqW_indicator_preimage_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Pointwise
open scoped ENNReal
open PI PI.QuotMeasUniqW
namespace PI.QuotMeasUniqW
theorem _root_.solution : QmuWeight := by
  intro G _ _ _ _ _ _ _ _ H hH ν hν
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hVo : IsOpen (interior K) := isOpen_interior
  have hVK : interior K ⊆ K := interior_subset
  have h1V : (1 : G) ∈ interior K := mem_interior_iff_mem_nhds.2 hK1
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq G
  have hCo : ∀ n, IsOpen (d n • interior K) := fun n => hVo.smul (d n)
  have hCm : ∀ n, MeasurableSet (d n • interior K) := fun n => (hCo n).measurableSet
  have hind : ∀ n, Measurable ((d n • interior K).indicator (1 : G → ℝ≥0∞)) :=
    fun n => measurable_one.indicator (hCm n)
  refine ⟨fun x => ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * (d n • interior K).indicator 1 x,
    Measurable.ennreal_tsum fun n => (hind n).const_mul _, fun g => ?_⟩
  have hmg : ∀ n, Measurable fun h : H => (d n • interior K).indicator (1 : G → ℝ≥0∞) (g * (h : G)) :=
    fun n => (hind n).comp ((measurable_const_mul g).comp measurable_subtype_coe)
  have hterm : ∀ n, Measurable fun h : H =>
      (2⁻¹ : ℝ≥0∞) ^ n * (d n • interior K).indicator 1 (g * (h : G)) :=
    fun n => (hmg n).const_mul _
  have hM : ν {h : H | (h : G) ∈ K⁻¹ * K} ≠ ⊤ := by
    have hc : IsCompact (((↑) : H → G) ⁻¹' (K⁻¹ * K)) :=
      hH.isClosedEmbedding_subtypeVal.isCompact_preimage (hK.inv.mul hK)
    exact hc.measure_lt_top.ne
  have hle : ∀ n, ∫⁻ h, (d n • interior K).indicator 1 (g * (h : G)) ∂ν
      ≤ ν {h : H | (h : G) ∈ K⁻¹ * K} := by
    intro n
    refine hAvg_indicator_le ν (d n • interior K) K (d n) g ?_
    intro x hx
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul] at hx
    exact hVK hx
  show (∫⁻ h, ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * (d n • interior K).indicator 1 (g * (h : G)) ∂ν) ≠ 0 ∧
    (∫⁻ h, ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * (d n • interior K).indicator 1 (g * (h : G)) ∂ν) ≠ ⊤
  constructor
  · obtain ⟨n, hn⟩ : ∃ n, (d n)⁻¹ * g ∈ interior K := by
      have ho : IsOpen {x : G | x⁻¹ * g ∈ interior K} :=
        hVo.preimage (continuous_inv.mul continuous_const)
      exact hd.exists_mem_open ho ⟨g, by simpa using h1V⟩
    have hSo : IsOpen {h : H | g * (h : G) ∈ d n • interior K} :=
      (hCo n).preimage (continuous_const.mul continuous_subtype_val)
    have hS1 : (1 : H) ∈ {h : H | g * (h : G) ∈ d n • interior K} := by
      show g * ((1 : H) : G) ∈ d n • interior K
      rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
      simpa [mul_assoc] using hn
    have hpos : 0 < ν {h : H | g * (h : G) ∈ d n • interior K} := hSo.measure_pos ν ⟨1, hS1⟩
    have heq : ∫⁻ h, (d n • interior K).indicator 1 (g * (h : G)) ∂ν
        = ν {h : H | g * (h : G) ∈ d n • interior K} := by
      have hfun : (fun h : H => (d n • interior K).indicator (1 : G → ℝ≥0∞) (g * (h : G)))
          = ((fun h : H => g * (h : G)) ⁻¹' (d n • interior K)).indicator 1 := by
        funext h
        exact (indicator_preimage_one (fun h : H => g * (h : G)) (d n • interior K) h).symm
      rw [hfun]
      exact lintegral_indicator_one hSo.measurableSet
    apply ne_of_gt
    calc (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ n * ν {h : H | g * (h : G) ∈ d n • interior K} :=
          ENNReal.mul_pos (pow_ne_zero _ (by simp)) hpos.ne'
      _ = ∫⁻ h, (2⁻¹ : ℝ≥0∞) ^ n * (d n • interior K).indicator 1 (g * (h : G)) ∂ν := by
          rw [lintegral_const_mul _ (hmg n), heq]
      _ ≤ ∫⁻ h, ∑' m, (2⁻¹ : ℝ≥0∞) ^ m * (d m • interior K).indicator 1 (g * (h : G)) ∂ν :=
          lintegral_mono fun h => ENNReal.le_tsum
            (f := fun m => (2⁻¹ : ℝ≥0∞) ^ m * (d m • interior K).indicator 1 (g * (h : G))) n
  · rw [lintegral_tsum fun n => (hterm n).aemeasurable]
    refine ne_top_of_le_ne_top (b := ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * ν {h : H | (h : G) ∈ K⁻¹ * K}) ?_ ?_
    · rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.mul_ne_top (by simp) hM
    · refine ENNReal.tsum_le_tsum fun n => ?_
      rw [lintegral_const_mul _ (hmg n)]
      gcongr
      exact hle n
end PI.QuotMeasUniqW
