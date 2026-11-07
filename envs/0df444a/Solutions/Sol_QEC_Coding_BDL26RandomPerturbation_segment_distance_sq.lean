-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.segment_distance_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:43:13.988265+00:00
-- url     : https://prove2.me/submissions/d5e50b81-7f5e-4043-8b8c-913a7b15815a

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SegmentProjection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (a b z : Space) (t : ℝ) :
    ‖z-(a+t • (b-a))‖^2 =
      ‖z-a‖^2-2*t*inner ℝ (z-a) (b-a)+t^2*‖b-a‖^2 := by
  have he : z-(a+t • (b-a)) = (z-a)-t • (b-a) := by abel
  rw [he,norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring
end QEC.Coding.BDL26RandomPerturbation
