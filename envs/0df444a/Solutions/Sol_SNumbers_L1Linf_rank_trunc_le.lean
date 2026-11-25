-- Prove2me | solution 1 for SNumbers.L1Linf.rank_trunc_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:35:22.299356+00:00
-- url     : https://prove2.me/submissions/4234eb2b-4e34-4cd3-952c-b3ec9e9e490c

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
public import Theorems.Thm_SNumbers_L1Linf_incl_apply
public import Theorems.Thm_SNumbers_L1Linf_e_apply_self
public import Theorems.Thm_SNumbers_L1Linf_inclL1L2_apply
public import Theorems.Thm_SNumbers_L1Linf_inclL2Linf_apply
public import Theorems.Thm_SNumbers_L1Linf_inclL2Linf_single
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_SNumbers_rank_comp_le_of_euclidean
public import Theorems.Thm_SNumbers_signedSum_empty
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] John.rankOneSA_apply
attribute [local simp] SNumbers.Complexification.adjoint_complexify
attribute [local simp] SNumbers.Complexification.complexify_conj
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_snd
attribute [local simp] SNumbers.Complexification.norm_complexify
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] SNumbers.signedSum_empty
attribute [local simp] Submodule.liftQL_mkQL


attribute [local simp] SNumbers.L1Linf.incl_apply
attribute [local simp] SNumbers.L1Linf.e_apply_self
attribute [local simp] SNumbers.L1Linf.inclL1L2_apply
attribute [local simp] SNumbers.L1Linf.inclL2Linf_apply
attribute [local simp] SNumbers.L1Linf.inclL2Linf_single

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
variable (A : L2 𝕜 →L[𝕜] L1 𝕜) (B : Linf 𝕜 →L[𝕜] L2 𝕜)
namespace SNumbers.L1Linf
theorem _root_.solution (m : ℕ) : (trunc A m).rank ≤ (m : Cardinal) := by
  have h : trunc A m = (emb1 m).comp ((proj1 m).comp A) := by simp only [trunc]
  rw [h]
  exact rank_comp_le_of_euclidean _ _
end SNumbers.L1Linf
