-- Prove2me | solution 1 for SNumbers.exists_closed_codim_forall_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:16:28.639742+00:00
-- url     : https://prove2.me/submissions/127fff9b-a46f-4f8a-845a-166457cdba2f

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
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) {k : ℕ}
    (g : Fin k → (Y →L[𝕜] 𝕜)) :
    ∃ M : Submodule 𝕜 X, IsClosed (M : Set X) ∧
      Module.rank 𝕜 (X ⧸ M) ≤ (k : Cardinal) ∧ (∀ x ∈ M, ∀ i, g i (S x) = 0) := by
  set Φ : X →L[𝕜] (Fin k → 𝕜) := ContinuousLinearMap.pi (fun i => (g i).comp S) with hΦ
  refine ⟨LinearMap.ker (Φ : X →ₗ[𝕜] (Fin k → 𝕜)), Φ.isClosed_ker, ?_, ?_⟩
  · rw [(LinearMap.quotKerEquivRange (Φ : X →ₗ[𝕜] (Fin k → 𝕜))).rank_eq]
    calc Module.rank 𝕜 (LinearMap.range (Φ : X →ₗ[𝕜] (Fin k → 𝕜)))
        ≤ Module.rank 𝕜 (Fin k → 𝕜) := Submodule.rank_le _
      _ = (k : Cardinal) := rank_fin_fun k
  · intro x hx i
    have h0 := congrFun (LinearMap.mem_ker.mp hx) i
    simpa [hΦ] using h0
end SNumbers
