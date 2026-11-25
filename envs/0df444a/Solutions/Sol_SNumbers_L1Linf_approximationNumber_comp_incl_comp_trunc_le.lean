-- Prove2me | solution 1 for SNumbers.L1Linf.approximationNumber_comp_incl_comp_trunc_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:17:04.781816+00:00
-- url     : https://prove2.me/submissions/d82b0c0b-e36b-4b82-b0f0-14f1f61bd854

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
public import Theorems.Thm_SNumbers_L1Linf_approximationNumber_comp_incl_comp_le_of_rank
public import Theorems.Thm_SNumbers_L1Linf_rank_trunc_le
public import Theorems.Thm_SNumbers_L1Linf_norm_trunc_le

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
variable (A : L2 𝕜 →L[𝕜] L1 𝕜) (B : Linf 𝕜 →L[𝕜] L2 𝕜)
namespace SNumbers.L1Linf
theorem _root_.solution (m n : ℕ) :
    approximationNumber (B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (trunc A m))) n
      ≤ ‖A‖ * ‖B‖ / (n + 1) := by
  refine (approximationNumber_comp_incl_comp_le_of_rank (trunc A m) B
    (rank_trunc_le A m) n).trans ?_
  gcongr
  exact norm_trunc_le A m
end SNumbers.L1Linf
