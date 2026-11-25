-- Prove2me | solution 1 for SNumbers.L1Linf.norm_incl_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:10:58.744932+00:00
-- url     : https://prove2.me/submissions/82516a8e-7196-4611-9913-11ec7319c6b6

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

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
namespace SNumbers.L1Linf
theorem _root_.solution : ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _
end SNumbers.L1Linf
