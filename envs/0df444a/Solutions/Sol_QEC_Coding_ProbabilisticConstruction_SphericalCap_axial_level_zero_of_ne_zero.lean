-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.axial_level_zero_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:38:28.080968+00:00
-- url     : https://prove2.me/submissions/d5afdc5d-edb5-4c21-81a9-7ca143d4ea0f

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_measurePreserving
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_norm_sq_axial
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {c : ℝ} (hc : c ≠ 0) :
    (volume : Measure Ambient) {x | c * ‖x‖ = x 0} = 0 := by
  let L : Set Ambient := {x | c * ‖x‖ = x 0}
  have hLm : MeasurableSet L :=
    (isClosed_eq (continuous_const.mul continuous_norm) (by fun_prop)).measurableSet
  have hm : MeasurePreserving axialEquiv.symm (volume.prod volume) volume :=
    axialEquiv_measurePreserving.symm
  rw [← hm.measure_preimage_equiv L,
    Measure.prod_apply (hLm.preimage axialEquiv.symm.measurable)]
  have hsection : ∀ z : ℝ, volume (Prod.mk z ⁻¹' (axialEquiv.symm ⁻¹' L)) = 0 := by
    intro z
    apply measure_mono_null (t := sphere (0 : Transverse)
      (Real.sqrt (coneSlopeSq c * z^2)))
    · intro y hy
      have hn := norm_sq_axial (axialEquiv.symm (z,y))
      simp only [MeasurableEquiv.apply_symm_apply] at hn
      have hfst : (axialEquiv.symm (z,y)) 0 = z := by
        change (axialEquiv (axialEquiv.symm (z,y))).1 = z
        rw [MeasurableEquiv.apply_symm_apply]
      change c * ‖axialEquiv.symm (z,y)‖ = (axialEquiv.symm (z,y)) 0 at hy
      rw [hfst] at hy
      have hs := congrArg (fun x : ℝ => x^2) hy
      rw [mul_pow,hn] at hs
      have hq : ‖y‖^2 = coneSlopeSq c * z^2 := by
        unfold coneSlopeSq
        field_simp
        nlinarith
      change dist y 0 = Real.sqrt (coneSlopeSq c * z^2)
      rw [dist_zero_right, ← hq, Real.sqrt_sq (norm_nonneg _)]
    · exact Measure.addHaar_sphere volume 0 _
  simp_rw [hsection, lintegral_zero]
end QEC.Coding.ProbabilisticConstruction.SphericalCap
