-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.inner_nonpos_distance_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:44:06.191644+00:00
-- url     : https://prove2.me/submissions/7afbcf6d-8147-401d-a0fc-9172f9268f02

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleMinimum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set
open scoped BigOperators InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (z y x : Space)
    (h : inner ℝ (z-y) (x-y) ≤ 0) : dist z y ≤ dist z x := by
  have he : z-x = (z-y)-(x-y) := by abel
  have hs : ‖z-y‖^2 ≤ ‖z-x‖^2 := by
    rw [he]
    have hn := norm_sub_sq_real (z-y) (x-y)
    nlinarith [sq_nonneg ‖x-y‖]
  rw [dist_eq_norm,dist_eq_norm]
  nlinarith [norm_nonneg (z-y),norm_nonneg (z-x)]
end QEC.Coding.BDL26RandomPerturbation
