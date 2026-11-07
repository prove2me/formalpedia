-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.openCone_subset_solid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:38:18.765245+00:00
-- url     : https://prove2.me/submissions/2dcf7090-2358-4ead-a8be-ed0e5221dcaf

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_displacement_norm
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u : Sphere) (c : ℝ) :
    Ioo (0 : ℝ) 1 • ((↑) '' cap u c) ⊆ solidCapCone u c := by
  rintro x ⟨r,hr,y,⟨s,hs,rfl⟩,rfl⟩
  have hn : ‖r • (s : Space)‖ = r := displacement_norm r hr.1.le s
  change ‖r • (s : Space)‖ ≤ 1 ∧
    c * ‖r • (s : Space)‖ ≤ inner ℝ (u : Space) (r • (s : Space))
  rw [hn, real_inner_smul_right]
  exact ⟨hr.2.le, by simpa [mul_comm] using mul_le_mul_of_nonneg_left hs hr.1.le⟩
end QEC.Coding.ProbabilisticConstruction.SphericalCap
