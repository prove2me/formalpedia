-- Prove2me | solution 1 for SNumbers.L1Linf.norm_T1_apply_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:30:04.452817+00:00
-- url     : https://prove2.me/submissions/db1ca924-c9fc-4731-b2c1-1747124d0be8

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
public import Theorems.Thm_SNumbers_norm_sq_eq_tsum_norm_sq


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
variable (A : L2 𝕜 →L[𝕜] L1 𝕜) (B : Linf 𝕜 →L[𝕜] L2 𝕜)
namespace SNumbers.L1Linf
theorem _root_.solution (x : L2 𝕜) :
    ‖T1 A x‖ ^ 2 = ∑' j, ‖(inner 𝕜 (row A j) x : 𝕜)‖ ^ 2 := by
  rw [norm_sq_eq_tsum_norm_sq]
  exact tsum_congr fun j => by rw [inner_row]; rfl
end SNumbers.L1Linf
