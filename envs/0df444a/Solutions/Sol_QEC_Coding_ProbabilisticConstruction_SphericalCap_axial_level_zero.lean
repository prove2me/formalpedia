-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.axial_level_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:39:20.819196+00:00
-- url     : https://prove2.me/submissions/7337dd7a-416a-40b2-8519-453eb41664a9

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axial_level_zero_of_ne_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_measurePreserving
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (c : ℝ) :
    (volume : Measure Ambient) {x | c * ‖x‖ = x 0} = 0 := by
  by_cases hc : c = 0
  · subst c
    let L : Set Ambient := {x | (0:ℝ) * ‖x‖ = x 0}
    have hLm : MeasurableSet L :=
      (isClosed_eq (continuous_const.mul continuous_norm) (by fun_prop)).measurableSet
    have hm : MeasurePreserving axialEquiv.symm (volume.prod volume) volume :=
      axialEquiv_measurePreserving.symm
    rw [← hm.measure_preimage_equiv L,
      Measure.prod_apply (hLm.preimage axialEquiv.symm.measurable)]
    calc
      _ = ∫⁻ z : ℝ, (0 : ℝ≥0∞) := by
        apply lintegral_congr_ae
        filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with z hz
        have he : Prod.mk z ⁻¹' (axialEquiv.symm ⁻¹' L) = ∅ := by
          ext y
          have hfst : (axialEquiv.symm (z,y)) 0 = z := by
            change (axialEquiv (axialEquiv.symm (z,y))).1 = z
            rw [MeasurableEquiv.apply_symm_apply]
          simp [L,hfst,hz,eq_comm]
        rw [he,measure_empty]
      _ = 0 := lintegral_zero
  · exact axial_level_zero_of_ne_zero hc
end QEC.Coding.ProbabilisticConstruction.SphericalCap
