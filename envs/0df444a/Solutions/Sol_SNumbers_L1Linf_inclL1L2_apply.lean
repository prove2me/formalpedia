-- Prove2me | solution 1 for SNumbers.L1Linf.inclL1L2_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:41:16.844836+00:00
-- url     : https://prove2.me/submissions/86fbf0a7-15c4-44b6-9e26-4d1ebf24b937

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
theorem _root_.solution (f : L1 𝕜) (i : ℕ) :
    ((inclL1L2 : L1 𝕜 →L[𝕜] L2 𝕜) f) i = f i := rfl
end SNumbers.L1Linf
