-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.axialCone_section_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:37:11.305182+00:00
-- url     : https://prove2.me/submissions/91752790-ab8a-4a2f-94f7-9c60546fa8c8

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_AxialCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_norm_sq_axial
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {c z : ℝ} (hc0 : 0 < c)
    (hz : z < 0 ∨ 1 < z) :
    {y : Transverse | axialEquiv.symm (z, y) ∈ axialCone c} = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y h
  have hnorm := norm_sq_axial (axialEquiv.symm (z, y))
  simp only [MeasurableEquiv.apply_symm_apply] at hnorm
  have hfst : (axialEquiv.symm (z, y)) 0 = z := by
    change (axialEquiv (axialEquiv.symm (z, y))).1 = z
    rw [MeasurableEquiv.apply_symm_apply]
  change ‖axialEquiv.symm (z, y)‖ ≤ 1 ∧
    c * ‖axialEquiv.symm (z, y)‖ ≤ (axialEquiv.symm (z, y)) 0 at h
  rw [hfst] at h
  rcases hz with hz | hz
  · exact (not_le_of_gt hz) ((mul_nonneg hc0.le (norm_nonneg _)).trans h.2)
  · nlinarith [norm_nonneg (axialEquiv.symm (z, y)), sq_nonneg ‖y‖]
end QEC.Coding.ProbabilisticConstruction.SphericalCap
