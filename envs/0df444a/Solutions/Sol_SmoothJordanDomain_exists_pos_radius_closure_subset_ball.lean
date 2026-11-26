-- Prove2me | solution 1 for SmoothJordanDomain.exists_pos_radius_closure_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:08:21.732439+00:00
-- url     : https://prove2.me/submissions/df4ae8e7-7520-4964-ba48-591c777ce0b6

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_SmoothJordanCompact
import Theorems.Thm_SmoothJordanDomain_isCompact_closure

set_option autoImplicit false
open Complex Metric Set
namespace SmoothJordanDomain
theorem _root_.solution
    (Omega : SmoothJordanDomain) (c : ℂ) :
    ∃ R : ℝ, 0 < R ∧ closure Omega.carrier ⊆ Metric.ball c R :=
  Omega.isCompact_closure.isBounded.subset_ball_lt 0 c
end SmoothJordanDomain
