-- Prove2me | solution 1 for SNumbers.L1Linf.norm_adjoint_T2_apply_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:36:04.156288+00:00
-- url     : https://prove2.me/submissions/a324b5ca-dd8d-4dcc-94a7-a4ccb5e9587a

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
public import Theorems.Thm_SNumbers_L1Linf_adjoint_T2_coord
public import Theorems.Thm_SNumbers_norm_sq_eq_tsum_norm_sq


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
variable (A : L2 𝕜 →L[𝕜] L1 𝕜) (B : Linf 𝕜 →L[𝕜] L2 𝕜)
namespace SNumbers.L1Linf
theorem _root_.solution (y : L2 𝕜) :
    ‖ContinuousLinearMap.adjoint (T2 B) y‖ ^ 2 = ∑' j, ‖(inner 𝕜 (col B j) y : 𝕜)‖ ^ 2 := by
  rw [norm_sq_eq_tsum_norm_sq]
  exact tsum_congr fun j => by rw [adjoint_T2_coord]
end SNumbers.L1Linf
