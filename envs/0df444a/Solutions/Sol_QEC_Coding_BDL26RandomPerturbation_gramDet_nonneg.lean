-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.gramDet_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:52:02.675575+00:00
-- url     : https://prove2.me/submissions/6e8761a5-4494-4b09-8c97-0f0f8565ff60

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SegmentProjection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (b c : Space) : 0 ≤ gramDet b c := by
  have h := real_inner_mul_inner_self_le b c
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at h
  unfold gramDet
  nlinarith
end QEC.Coding.BDL26RandomPerturbation
