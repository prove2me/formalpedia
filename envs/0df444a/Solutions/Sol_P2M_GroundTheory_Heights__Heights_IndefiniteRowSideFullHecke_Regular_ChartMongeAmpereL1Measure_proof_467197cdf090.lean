-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_proof_467197cdf090
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:00:09.287968+00:00
-- url     : https://prove2.me/submissions/c052438b-8261-4906-a6c3-4892262f593c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ChartMongeAmpereL1Hypotheses
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_AestronglyMeasurableMapSymm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_aestronglyMeasurable_map_symm_b00e7b327fe5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_maMeasure_le_smul_sum_62af3e70de23
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot maMeasure ChartPartition locDens)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
namespace ChartMongeAmpereL1Measure
theorem _root_.solution : ChartMongeAmpereL1Measure.Statement := by
  intro X _ _ _ _ _ D A P om hom _hpos g t₀ ht₀ hg
  set μ := maMeasure A (fun _ : Fin D => om) with hμ
  obtain ⟨C, hC, hle⟩ :=
    ChartMongeAmpereL1Measure.maMeasure_le_smul_sum A P (fun _ => om) (fun _ => hom)
  set ν := ∑ k, (volume.restrict (P.chartMid k)).map (P.chart k).symm with hν
  have hMm : ∀ k, MeasurableSet (P.chartMid k) := fun k =>
    ((P.chart k).isOpen_inter_preimage_symm (P.isOpen_mid k)).measurableSet
  have hsy : ∀ k, AEMeasurable (P.chart k).symm (volume.restrict (P.chartMid k)) := fun k =>
    ((P.chart k).continuousOn_symm.mono inter_subset_left).aemeasurable (hMm k)
  have hnn : ∀ t, 0 ≤ ∑ k, ∫ y in P.chartMid k, |g t ((P.chart k).symm y)| := fun t =>
    Finset.sum_nonneg fun k _ => integral_nonneg fun y => abs_nonneg _
  have key : ∀ t, 0 < t → t < t₀ → Integrable (g t) μ ∧
      ∫ x, |g t x| ∂μ ≤ C.toReal * ∑ k, ∫ y in P.chartMid k, |g t ((P.chart k).symm y)| := by
    intro t ht ht'
    have hI : ∀ k, IntegrableOn (fun y => g t ((P.chart k).symm y)) (P.chartMid k) :=
      fun k => (hg k).1 t ht ht'
    have hmk : ∀ k, AEStronglyMeasurable (g t)
        ((volume.restrict (P.chartMid k)).map (P.chart k).symm) := fun k =>
      ChartMongeAmpereL1Measure.aestronglyMeasurable_map_symm (P.chart k) (hMm k) inter_subset_left
        (hI k).aestronglyMeasurable
    have hmν : AEStronglyMeasurable (g t) ν := by
      rw [hν, ← Measure.sum_fintype]
      exact aestronglyMeasurable_sum_measure_iff.2 hmk
    have hmμ : AEStronglyMeasurable (g t) μ := (hmν.smul_measure C).mono_measure hle
    have hlin : ∫⁻ x, ‖g t x‖ₑ ∂μ ≤
        C * ∑ k, ENNReal.ofReal (∫ y in P.chartMid k, |g t ((P.chart k).symm y)|) := by
      calc ∫⁻ x, ‖g t x‖ₑ ∂μ ≤ ∫⁻ x, ‖g t x‖ₑ ∂(C • ν) := lintegral_mono' hle le_rfl
        _ = C * ∑ k, ∫⁻ x, ‖g t x‖ₑ ∂((volume.restrict (P.chartMid k)).map (P.chart k).symm) := by
          rw [lintegral_smul_measure, hν, lintegral_finsetSum_measure, smul_eq_mul]
        _ = _ := by
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [lintegral_map' (hmk k).enorm (hsy k), ← ofReal_integral_norm_eq_lintegral_enorm (hI k)]
          simp only [Real.norm_eq_abs]
    have hfin : C * ∑ k, ENNReal.ofReal (∫ y in P.chartMid k, |g t ((P.chart k).symm y)|) =
        ENNReal.ofReal (C.toReal * ∑ k, ∫ y in P.chartMid k, |g t ((P.chart k).symm y)|) := by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC,
        ENNReal.ofReal_sum_of_nonneg fun k _ => integral_nonneg fun y => abs_nonneg _]
    rw [hfin] at hlin
    have hInt : Integrable (g t) μ := ⟨hmμ, lt_of_le_of_lt hlin ENNReal.ofReal_lt_top⟩
    refine ⟨hInt, ?_⟩
    have h1 : ENNReal.ofReal (∫ x, |g t x| ∂μ) = ∫⁻ x, ‖g t x‖ₑ ∂μ := by
      rw [← ofReal_integral_norm_eq_lintegral_enorm hInt]
      simp only [Real.norm_eq_abs]
    rw [← h1] at hlin
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg ENNReal.toReal_nonneg (hnn t))).1 hlin
  refine ⟨fun t ht ht' => (key t ht ht').1, ?_⟩
  have hlim : Tendsto (fun t => C.toReal * ∑ k, ∫ y in P.chartMid k, |g t ((P.chart k).symm y)|)
      (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_finsetSum Finset.univ fun k _ => (hg k).2).const_mul C.toReal
    simpa using this
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 t₀ := Ioo_mem_nhdsGT ht₀
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall fun t => integral_nonneg fun x => abs_nonneg _
  · exact hev.mono fun t ht => (key t ht.1 ht.2).2
end ChartMongeAmpereL1Measure
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
