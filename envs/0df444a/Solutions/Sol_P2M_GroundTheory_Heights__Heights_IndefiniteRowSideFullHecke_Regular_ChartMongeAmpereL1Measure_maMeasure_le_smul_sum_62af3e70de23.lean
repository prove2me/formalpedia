-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_maMeasure_le_smul_sum_62af3e70de23
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:13:32.776279+00:00
-- url     : https://prove2.me/submissions/230cd1b1-f20e-4eee-920d-5d3745b3aacd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ChartMongeAmpereL1Hypotheses
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_AestronglyMeasurableMapSymm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_lintegral_chart_change_e9133996c1cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_density_bound_b839bd65922a
import Theorems.Thm_ReciprocityTheory_AnForm_M_chi_comp_continuousOn
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensCont
import Theorems.Thm_ReciprocityTheory_AnForm_M_maMeasure_eq_sum
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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartMongeAmpereL1Measure
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartMongeAmpereL1Measure
theorem _root_.solution {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas D X) (P : PotentialCharts A)
    (Φ : Fin D → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      maMeasure A Φ ≤ C • ∑ k, (volume.restrict (P.chartMid k)).map (P.chart k).symm := by
  by_cases hne : Nonempty (ChartPartition A)
  swap
  · refine ⟨0, ENNReal.zero_ne_top, ?_⟩
    simp [maMeasure, dif_neg hne]
  set Q := hne.some with hQ
  choose c hc hcb using fun j => density_bound A Q Φ hΦ j
  choose B hB hBb using fun (j : Fin A.n) (k : Fin P.N) =>
    lintegral_chart_change (A.chart j) (P.chart k) ((P.compat k j).2) (isClosed_tsupport (Q.χ j))
      (Q.tsupport_subset j) (P.isOpen_mid k) (P.closure_mid k)
  refine ⟨∑ j, ∑ k, c j * B j k, ?_, ?_⟩
  · exact ENNReal.sum_ne_top.2 fun j _ =>
      ENNReal.sum_ne_top.2 fun k _ => ENNReal.mul_ne_top (hc j) (hB j k)
  rw [Measure.le_iff]
  intro s hs
  set F : X → ℝ≥0∞ := s.indicator 1 with hF
  have hFm : Measurable F := measurable_const.indicator hs
  have hν : ∀ k, ((volume.restrict (P.chartMid k)).map (P.chart k).symm) s =
      ∫⁻ z in P.chartMid k, F ((P.chart k).symm z) := by
    intro k
    have hMm : MeasurableSet (P.chartMid k) :=
      ((P.chart k).isOpen_inter_preimage_symm (P.isOpen_mid k)).measurableSet
    have hsy : AEMeasurable (P.chart k).symm (volume.restrict (P.chartMid k)) :=
      ((P.chart k).continuousOn_symm.mono inter_subset_left).aemeasurable hMm
    rw [← lintegral_indicator_one hs, ← hF, lintegral_map' hFm.aemeasurable hsy]
  have hμ : ∀ j, ReciprocityTheory.AnForm.M.chartMeasure A Q Φ j s ≤
      ∑ k, c j * B j k * ∫⁻ z in P.chartMid k, F ((P.chart k).symm z) := by
    intro j
    have hTm := (A.chart j).open_target.measurableSet
    have hsymm : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target) :=
      (A.chart j).continuousOn_symm.aemeasurable hTm
    have hsymm' := hsymm.mono_ac (withDensity_absolutelyContinuous
      (volume.restrict (A.chart j).target)
      fun y => ENNReal.ofReal (Q.χ j ((A.chart j).symm y) * locDens A Φ j y))
    have hw : AEMeasurable (fun y => ENNReal.ofReal (Q.χ j ((A.chart j).symm y) * locDens A Φ j y))
        (volume.restrict (A.chart j).target) :=
      (((ReciprocityTheory.AnForm.M.chi_comp_continuousOn Q j).mul
        (ReciprocityTheory.AnForm.M.locDensCont A Φ hΦ j)).aemeasurable hTm).ennreal_ofReal
    have hpiece : ∀ k, AEMeasurable
        (fun y => (tsupport (Q.χ j) ∩ P.mid k).indicator F ((A.chart j).symm y))
        (volume.restrict (A.chart j).target) := fun k =>
      (hFm.indicator ((isClosed_tsupport _).measurableSet.inter
        (P.isOpen_mid k).measurableSet)).comp_aemeasurable hsymm
    calc ReciprocityTheory.AnForm.M.chartMeasure A Q Φ j s
        = ∫⁻ y in (A.chart j).target, ENNReal.ofReal (Q.χ j ((A.chart j).symm y) *
            locDens A Φ j y) * F ((A.chart j).symm y) := by
          unfold ReciprocityTheory.AnForm.M.chartMeasure
          rw [← lintegral_indicator_one hs, ← hF, lintegral_map' hFm.aemeasurable hsymm']
          exact lintegral_withDensity_eq_lintegral_mul₀ hw (hFm.comp_aemeasurable hsymm)
      _ ≤ ∫⁻ y in (A.chart j).target,
            ∑ k, c j * (tsupport (Q.χ j) ∩ P.mid k).indicator F ((A.chart j).symm y) := by
          refine setLIntegral_mono' hTm fun y hy => ?_
          have h1 := hcb j y hy
          by_cases hx : (A.chart j).symm y ∈ tsupport (Q.χ j)
          · rw [indicator_of_mem hx] at h1
            obtain ⟨k0, hk0⟩ := P.cover ((A.chart j).symm y)
            have hk0' := P.inner_subset_mid k0 hk0
            calc _ ≤ c j * F ((A.chart j).symm y) := by gcongr
              _ = c j * (tsupport (Q.χ j) ∩ P.mid k0).indicator F ((A.chart j).symm y) := by
                rw [indicator_of_mem (show (A.chart j).symm y ∈ tsupport (Q.χ j) ∩ P.mid k0
                  from ⟨hx, hk0'⟩)]
              _ ≤ _ := Finset.single_le_sum (f := fun k =>
                  c j * (tsupport (Q.χ j) ∩ P.mid k).indicator F ((A.chart j).symm y))
                  (fun _ _ => zero_le) (Finset.mem_univ k0)
          · rw [indicator_of_notMem hx] at h1
            have : ENNReal.ofReal (Q.χ j ((A.chart j).symm y) * locDens A Φ j y) = 0 :=
              le_antisymm h1 zero_le
            rw [this, zero_mul]
            exact zero_le
      _ = ∑ k, c j * ∫⁻ y in (A.chart j).target,
            (tsupport (Q.χ j) ∩ P.mid k).indicator F ((A.chart j).symm y) := by
          rw [lintegral_finsetSum' _ fun k _ => (hpiece k).const_mul (c j)]
          exact Finset.sum_congr rfl fun k _ => lintegral_const_mul' _ _ (hc j)
      _ ≤ ∑ k, c j * B j k * ∫⁻ z in P.chartMid k, F ((P.chart k).symm z) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [mul_assoc]
          gcongr
          exact hBb j k F
  rw [ReciprocityTheory.AnForm.M.maMeasure_eq_sum A Φ hne, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  simp only [hν]
  calc ∑ j, ReciprocityTheory.AnForm.M.chartMeasure A hne.some Φ j s
      ≤ ∑ j, ∑ k, c j * B j k * ∫⁻ z in P.chartMid k, F ((P.chart k).symm z) :=
        Finset.sum_le_sum fun j _ => hμ j
    _ ≤ ∑ j, ∑ k, c j * B j k * ∑ k', ∫⁻ z in P.chartMid k', F ((P.chart k').symm z) := by
        gcongr with j _ k _
        exact Finset.single_le_sum (f := fun k' => ∫⁻ z in P.chartMid k', F ((P.chart k').symm z))
          (fun _ _ => zero_le) (Finset.mem_univ k)
    _ = _ := by simp_rw [Finset.sum_mul]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartMongeAmpereL1Measure
