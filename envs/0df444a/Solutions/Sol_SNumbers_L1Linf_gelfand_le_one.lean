-- Prove2me | solution 1 for SNumbers.L1Linf.gelfand_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:15:41.238933+00:00
-- url     : https://prove2.me/submissions/2f014ce1-8ef9-4b51-b418-790dee766c8e

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
public import Theorems.Thm_SNumbers_L1Linf_norm_incl_le
public import Theorems.Thm_SNumbers_gelfandNumber_le_norm


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
namespace SNumbers.L1Linf
theorem _root_.solution (n : ℕ) :
    gelfandNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n ≤ 1 :=
  (gelfandNumber_le_norm _ _).trans norm_incl_le
end SNumbers.L1Linf
