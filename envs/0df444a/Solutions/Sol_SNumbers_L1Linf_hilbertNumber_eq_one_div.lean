-- Prove2me | solution 1 for SNumbers.L1Linf.hilbertNumber_eq_one_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:48:02.725002+00:00
-- url     : https://prove2.me/submissions/757aab9a-87a9-442f-9e63-2b177e428b7b

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
public import Theorems.Thm_SNumbers_L1Linf_one_div_le_hilbertNumber
public import Theorems.Thm_SNumbers_L1Linf_hilbertNumber_le_one_div

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
namespace SNumbers.L1Linf
theorem _root_.solution (n : ℕ) :
    hilbertNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n = (1 : ℝ) / (n + 1) :=
  le_antisymm (hilbertNumber_le_one_div n) (one_div_le_hilbertNumber n)
end SNumbers.L1Linf
