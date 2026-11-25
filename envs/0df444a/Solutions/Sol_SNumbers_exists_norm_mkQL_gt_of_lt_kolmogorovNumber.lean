-- Prove2me | solution 1 for SNumbers.exists_norm_mkQL_gt_of_lt_kolmogorovNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:19:15.095806+00:00
-- url     : https://prove2.me/submissions/ed0ea042-fc28-4c32-98f2-317933f9ca5a

module
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_SingularValuesFinDim
public import Definitions.Def_BasicResults_GarlingGordon
public import Definitions.Def_BasicResults_KadetsSnobar
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_SNumbers_Inequalities
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
public import Theorems.Thm_SNumbers_kolmogorovNumber_le_deviation
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
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X] [CompleteSpace Y]
omit [CompleteSpace X] [CompleteSpace Y]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) {k : ℕ} {V : Submodule 𝕜 Y}
    (hV_rank : Module.rank 𝕜 V ≤ (k : Cardinal)) {c : ℝ} (hc : c < kolmogorovNumber S k) :
    ∃ x : X, ‖x‖ ≤ 1 ∧ c < ‖V.mkQL (S x)‖ := by
  have hlt : c < ‖V.mkQL.comp S‖ := lt_of_lt_of_le hc (kolmogorovNumber_le_deviation hV_rank)
  obtain ⟨x, hx, hxc⟩ := (V.mkQL.comp S).exists_lt_apply_of_lt_opNorm hlt
  exact ⟨x, hx.le, by simpa using hxc⟩
end SNumbers
