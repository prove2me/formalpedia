-- Prove2me | solution 1 for SNumbers.L1Linf.norm_projinf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:39:16.546528+00:00
-- url     : https://prove2.me/submissions/168e7c75-93ee-4614-beb9-a68a787b2dac

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
public import Theorems.Thm_SNumbers_L1Linf_norm_projinf_apply_le

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
namespace SNumbers.L1Linf
theorem _root_.solution (m : ℕ) :
    ‖(projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m))‖ ≤ Real.sqrt m :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (norm_projinf_apply_le m)
end SNumbers.L1Linf
