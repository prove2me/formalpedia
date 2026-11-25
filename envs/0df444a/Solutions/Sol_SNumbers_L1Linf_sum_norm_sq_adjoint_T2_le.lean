-- Prove2me | solution 1 for SNumbers.L1Linf.sum_norm_sq_adjoint_T2_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:38:47.746542+00:00
-- url     : https://prove2.me/submissions/7936c647-3587-4f70-851d-5b9ede09d6f7

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
public import Theorems.Thm_SNumbers_L1Linf_sum_norm_sq_col_le_norm_sq
public import Theorems.Thm_SNumbers_L1Linf_norm_adjoint_T2_apply_sq
public import Theorems.Thm_SVD_sum_norm_sq_apply_le_of_rows


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
variable (A : L2 𝕜 →L[𝕜] L1 𝕜) (B : Linf 𝕜 →L[𝕜] L2 𝕜)
namespace SNumbers.L1Linf
theorem _root_.solution {v : ℕ → L2 𝕜} (hv : SVD.OrthonormalOrZero 𝕜 v)
    (s : Finset ℕ) :
    ∑ k ∈ s, ‖ContinuousLinearMap.adjoint (T2 B) (v k)‖ ^ 2 ≤ ‖B‖ ^ 2 :=
  SVD.sum_norm_sq_apply_le_of_rows (norm_adjoint_T2_apply_sq B)
    (sum_norm_sq_col_le_norm_sq B) hv s
end SNumbers.L1Linf
