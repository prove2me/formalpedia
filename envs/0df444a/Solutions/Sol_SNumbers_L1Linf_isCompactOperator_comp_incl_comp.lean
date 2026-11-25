-- Prove2me | solution 1 for SNumbers.L1Linf.isCompactOperator_comp_incl_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:36:46.742107+00:00
-- url     : https://prove2.me/submissions/a03c012c-3d34-4237-8403-7ade2b80e3d5

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
public import Theorems.Thm_SNumbers_L1Linf_rank_comp_incl_comp_le
public import Theorems.Thm_SVD_isCompactOperator_of_rank_le


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
variable (A : L2 𝕜 →L[𝕜] L1 𝕜) (B : Linf 𝕜 →L[𝕜] L2 𝕜)
namespace SNumbers.L1Linf
theorem _root_.solution {m : ℕ} (hrank : A.rank ≤ (m : Cardinal)) :
    IsCompactOperator (B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp A)) :=
  SVD.isCompactOperator_of_rank_le ((rank_comp_incl_comp_le A B).trans hrank)
end SNumbers.L1Linf
