-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.displacementCap_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:37:50.75165+00:00
-- url     : https://prove2.me/submissions/9f4cfc95-3995-403b-a0cb-449c59cbd38a

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_displacement_norm
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {R : ℝ} (hR : 0 < R) (u : Sphere) (c : ℝ) :
    (fun s : Sphere => R • (s : Space)) ⁻¹' displacementCap R u c = cap u c := by
  ext s
  simp only [displacementCap,cap,mem_preimage,mem_setOf_eq,
    displacement_norm R hR.le, true_and,real_inner_smul_right]
  exact mul_le_mul_iff_right₀ hR
end QEC.Coding.ProbabilisticConstruction.SphericalCap
