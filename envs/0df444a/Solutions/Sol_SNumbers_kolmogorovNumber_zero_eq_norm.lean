-- Prove2me | solution 1 for SNumbers.kolmogorovNumber_zero_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:13:38.508346+00:00
-- url     : https://prove2.me/submissions/f50fc6bd-229f-4f16-805f-0fd4fb31a7ef

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
public import Theorems.Thm_SNumbers_kolmogorovSet_nonempty
public import Theorems.Thm_SNumbers_kolmogorovNumber_le_deviation
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] Submodule.liftQL_mkQL


section
@[expose] public section
universe u
open scoped Cardinal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
private lemma norm_mk_bot (y : Y) :
    ‖((⊥ : Submodule 𝕜 Y).mkQ y : Y ⧸ (⊥ : Submodule 𝕜 Y))‖ = ‖y‖ := by
  refine le_antisymm ?_ ?_
  · simpa using _root_.Submodule.Quotient.norm_mk_le (S := (⊥ : Submodule 𝕜 Y)) y
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨y', hy'_eq, hy'_lt⟩ :=
      Submodule.Quotient.norm_mk_lt
        ((⊥ : Submodule 𝕜 Y).mkQ y : Y ⧸ (⊥ : Submodule 𝕜 Y)) hε
    -- `Submodule.Quotient.mk y' = mkQ y` and `mkQ y' = mkQ y`, so `y' - y ∈ ⊥ = {0}`.
    have h_eq : y' = y := by
      have hker : y' - y ∈ (⊥ : Submodule 𝕜 Y) := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hy'_eq]
        change (⊥ : Submodule 𝕜 Y).mkQ y - (⊥ : Submodule 𝕜 Y).mkQ y = 0
        simp
      rwa [Submodule.mem_bot, sub_eq_zero] at hker
    have h_norm_eq : ‖y‖ = ‖y'‖ := by rw [h_eq]
    rw [h_norm_eq]
    exact hy'_lt.le
private lemma deviationFromSubspace_bot (S : X →L[𝕜] Y) :
    deviationFromSubspace S (⊥ : Submodule 𝕜 Y) = ‖S‖ := by
  unfold deviationFromSubspace
  refine le_antisymm ?_ ?_
  · -- `‖(⊥).mkQL ∘ S‖ ≤ ‖S‖`: pointwise `‖[S x]‖ = ‖S x‖ ≤ ‖S‖ * ‖x‖`.
    refine opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [coe_comp, Function.comp_apply, Submodule.mkQL_apply, norm_mk_bot]
    exact S.le_opNorm x
  · -- `‖S‖ ≤ ‖(⊥).mkQL ∘ S‖`: pointwise `‖S x‖ = ‖[S x]‖ ≤ ‖(⊥).mkQL ∘ S‖ * ‖x‖`.
    refine opNorm_le_bound _
      (norm_nonneg ((⊥ : Submodule 𝕜 Y).mkQL.comp S)) fun x => ?_
    rw [← norm_mk_bot (𝕜 := 𝕜) (S x)]
    change ‖((⊥ : Submodule 𝕜 Y).mkQL.comp S) x‖ ≤ _
    exact ((⊥ : Submodule 𝕜 Y).mkQL.comp S).le_opNorm x
variable [CompleteSpace 𝕜]
end SNumbers
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) :
    kolmogorovNumber S 0 = ‖S‖ := by
  refine le_antisymm ?_ ?_
  · have h_rank : Module.rank 𝕜 (⊥ : Submodule 𝕜 Y) ≤ ((0 : ℕ) : Cardinal) := by
      rw [rank_bot]; exact_mod_cast Nat.zero_le 0
    exact (kolmogorovNumber_le_deviation h_rank).trans_eq (deviationFromSubspace_bot S)
  · refine le_csInf (kolmogorovSet_nonempty S 0) ?_
    rintro _ ⟨V, hV, rfl⟩
    have hV_bot : V = ⊥ := by
      rw [← Submodule.rank_eq_zero]
      exact le_antisymm (by exact_mod_cast hV) zero_le
    rw [hV_bot, deviationFromSubspace_bot]
end SNumbers
