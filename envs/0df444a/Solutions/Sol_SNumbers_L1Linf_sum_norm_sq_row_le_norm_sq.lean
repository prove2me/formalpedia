-- Prove2me | solution 1 for SNumbers.L1Linf.sum_norm_sq_row_le_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:37:45.038821+00:00
-- url     : https://prove2.me/submissions/f7b350b2-8801-449f-b742-fdb66f43d118

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_AddOns_Approximable
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Sequences
public import Definitions.Def_SNumbers_Examples_IdentityL1Linfty
public import Theorems.Thm_SNumbers_L1Linf_inner_row
public import Theorems.Thm_SNumbers_sum_norm_sq_row_le


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
variable (A : L2 𝕜 →L[𝕜] L1 𝕜) (B : Linf 𝕜 →L[𝕜] L2 𝕜)
namespace SNumbers.L1Linf
theorem _root_.solution (J : Finset ℕ) : ∑ j ∈ J, ‖row A j‖ ^ 2 ≤ ‖A‖ ^ 2 :=
  sum_norm_sq_row_le A (inner_row A) J
end SNumbers.L1Linf
