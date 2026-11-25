-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_maMeasure_compact_eq_d1a3cdb552e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:08:00.644425+00:00
-- url     : https://prove2.me/submissions/02e6235c-a56e-4ae9-ab56-fca17b370f21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PMongeAmpereComparison
import Theorems.Thm_ReciprocityTheory_AnForm_M_chi_comp_continuousOn
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_integrableOn_target_of_closed
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensCont
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDens_nonneg_of_psh
import Theorems.Thm_ReciprocityTheory_AnForm_M_mInt_eq_integralWith
import Theorems.Thm_ReciprocityTheory_AnForm_M_maMeasure_eq_sum
import Theorems.Thm_ReciprocityTheory_AnForm_M_map_withDensity_integrable_integral
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
namespace GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (hne : Nonempty (ChartPartition A)) (hΦ : ∀ i, IsPotential A (Φ i))
    (hPsh : ∀ i, IsPsh A (Φ i)) {K : Set X} (hK : IsCompact K) :
    maMeasure A Φ K = ENNReal.ofReal (mInt A Φ (K.indicator 1)) := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hg : Measurable (K.indicator (1 : X → ℝ)) := measurable_const.indicator hKm
  have hw0 : ∀ j, ∀ y ∈ (A.chart j).target,
      0 ≤ hne.some.χ j ((A.chart j).symm y) * locDens A Φ j y := fun j y hy =>
    mul_nonneg (hne.some.nonneg j _) (locDens_nonneg_of_psh A Φ hΦ hPsh j hy)
  have hj : ∀ j, chartMeasure A hne.some Φ j K =
      ENNReal.ofReal (∫ y in (A.chart j).target, K.indicator 1 ((A.chart j).symm y) *
        (hne.some.χ j ((A.chart j).symm y) * locDens A Φ j y)) := by
    intro j
    have hw : ContinuousOn (fun y => hne.some.χ j ((A.chart j).symm y) * locDens A Φ j y)
        (A.chart j).target :=
      (chi_comp_continuousOn hne.some j).mul (locDensCont A Φ hΦ j)
    have key := map_withDensity_integrable_integral (A.chart j).open_target
      (A.chart j).continuousOn_symm hw (hw0 j) hg
    have hZ : IsCompact (K ∩ tsupport (hne.some.χ j)) := hK.inter_right (isClosed_tsupport _)
    have hZs : K ∩ tsupport (hne.some.χ j) ⊆ (A.chart j).source := fun x hx =>
      hne.some.tsupport_subset j hx.2
    have hC : IsCompact ((A.chart j) '' (K ∩ tsupport (hne.some.χ j))) :=
      hZ.image_of_continuousOn ((A.chart j).continuousOn.mono hZs)
    have hCT : (A.chart j) '' (K ∩ tsupport (hne.some.χ j)) ⊆ (A.chart j).target :=
      Set.image_subset_iff.mpr fun x hx => (A.chart j).map_source (hZs hx)
    have hCm : MeasurableSet ((A.chart j) '' (K ∩ tsupport (hne.some.χ j))) :=
      hC.isClosed.measurableSet
    have hint : IntegrableOn (fun y => K.indicator 1 ((A.chart j).symm y) *
        (hne.some.χ j ((A.chart j).symm y) * locDens A Φ j y)) (A.chart j).target := by
      refine integrableOn_target_of_closed (A.chart j) (Z := K ∩ tsupport (hne.some.χ j)) ?_ ?_
      · intro y _ hyZ
        by_cases hyK : (A.chart j).symm y ∈ K
        · have : (A.chart j).symm y ∉ tsupport (hne.some.χ j) := fun h => hyZ ⟨hyK, h⟩
          simp [image_eq_zero_of_notMem_tsupport this]
        · simp [hyK]
      · have hwi : IntegrableOn (fun y => hne.some.χ j ((A.chart j).symm y) * locDens A Φ j y)
            ((A.chart j) '' (K ∩ tsupport (hne.some.χ j))) :=
          (hw.mono hCT).integrableOn_compact hC
        have hs1 : AEMeasurable (A.chart j).symm
            (volume.restrict ((A.chart j) '' (K ∩ tsupport (hne.some.χ j)))) :=
          ((A.chart j).continuousOn_symm.mono hCT).aemeasurable hCm
        refine Integrable.mono' hwi
          ((hg.comp_aemeasurable hs1).mul ((hw.mono hCT).aemeasurable hCm)).aestronglyMeasurable
          (ae_restrict_of_forall_mem hCm fun y hy => ?_)
        have hy0 := hw0 j y (hCT hy)
        have h1 : |K.indicator (1 : X → ℝ) ((A.chart j).symm y)| ≤ 1 := by
          by_cases h : (A.chart j).symm y ∈ K <;> simp [h]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hy0]
        exact mul_le_of_le_one_left hy0 h1
    have hi : Integrable (K.indicator (1 : X → ℝ)) (chartMeasure A hne.some Φ j) := key.1.mpr hint
    have e2 : ∫ x, K.indicator (1 : X → ℝ) x ∂chartMeasure A hne.some Φ j =
        ∫ y in (A.chart j).target, K.indicator 1 ((A.chart j).symm y) *
          (hne.some.χ j ((A.chart j).symm y) * locDens A Φ j y) := key.2
    rw [← e2, ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)]
    have : (fun x => ENNReal.ofReal (K.indicator (1 : X → ℝ) x)) = K.indicator 1 := by
      funext x
      by_cases h : x ∈ K <;> simp [h]
    rw [this, lintegral_indicator_one hKm]
  rw [maMeasure_eq_sum A Φ hne]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, hj]
  have hsum := ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
    (f := fun j => ∫ y in (A.chart j).target, K.indicator (1 : X → ℝ) ((A.chart j).symm y) *
      (hne.some.χ j ((A.chart j).symm y) * locDens A Φ j y))
    fun j _ => setIntegral_nonneg (A.chart j).open_target.measurableSet fun y hy =>
      mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (hw0 j y hy)
  rw [← hsum]
  congr 1
  rw [mInt_eq_integralWith A Φ hne]
  unfold integralWith
  refine Finset.sum_congr rfl fun j _ => integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring
end GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
