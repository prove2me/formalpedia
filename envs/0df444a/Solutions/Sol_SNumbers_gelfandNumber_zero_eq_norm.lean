-- Prove2me | solution 1 for SNumbers.gelfandNumber_zero_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:04:33.522827+00:00
-- url     : https://prove2.me/submissions/5cf43849-b6f4-4141-8fa7-77c4102ea86a

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
public import Theorems.Thm_SNumbers_gelfandSet_nonempty
public import Theorems.Thm_SNumbers_gelfandNumber_le_deviation
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
private lemma deviationFromRestriction_top (S : X →L[𝕜] Y) :
    deviationFromRestriction S (⊤ : Submodule 𝕜 X) = ‖S‖ := by
  unfold deviationFromRestriction
  refine le_antisymm ?_ ?_
  · -- `‖S.comp ⊤.subtypeL‖ ≤ ‖S‖ * ‖⊤.subtypeL‖ ≤ ‖S‖`.
    calc ‖S.comp (⊤ : Submodule 𝕜 X).subtypeL‖
        ≤ ‖S‖ * ‖(⊤ : Submodule 𝕜 X).subtypeL‖ := opNorm_comp_le _ _
      _ ≤ ‖S‖ * 1 :=
          mul_le_mul_of_nonneg_left
            (⊤ : Submodule 𝕜 X).norm_subtypeL_le (norm_nonneg _)
      _ = ‖S‖ := mul_one _
  · -- For every `x : X`, `‖S x‖ ≤ ‖S.comp ⊤.subtypeL‖ * ‖x‖`.
    refine opNorm_le_bound _
      (norm_nonneg (S.comp (⊤ : Submodule 𝕜 X).subtypeL)) fun x => ?_
    have h_eq :
        S x = (S.comp (⊤ : Submodule 𝕜 X).subtypeL) ⟨x, Submodule.mem_top⟩ := rfl
    rw [h_eq]
    exact (S.comp (⊤ : Submodule 𝕜 X).subtypeL).le_opNorm
      ⟨x, Submodule.mem_top⟩
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
    gelfandNumber S 0 = ‖S‖ := by
  refine le_antisymm ?_ ?_
  · -- Take `M = ⊤`.
    have h_rank : Module.rank 𝕜 (X ⧸ (⊤ : Submodule 𝕜 X)) ≤ ((0 : ℕ) : Cardinal) := by
      have h0 : Module.rank 𝕜 (X ⧸ (⊤ : Submodule 𝕜 X)) = 0 :=
        rank_zero_iff.mpr inferInstance
      rw [h0]; exact_mod_cast Nat.zero_le 0
    have h_closed : IsClosed ((⊤ : Submodule 𝕜 X) : Set X) := by
      rw [Submodule.top_coe]; exact isClosed_univ
    exact (gelfandNumber_le_deviation h_closed h_rank).trans_eq
      (deviationFromRestriction_top S)
  · refine le_csInf (gelfandSet_nonempty S 0) ?_
    rintro _ ⟨M, _, hM_rank, rfl⟩
    -- `rank (X ⧸ M) ≤ 0` ⇒ `X ⧸ M` subsingleton ⇒ `M = ⊤`.
    have h_rank_zero : Module.rank 𝕜 (X ⧸ M) = 0 :=
      le_antisymm (by exact_mod_cast hM_rank) zero_le
    have h_subsingleton : Subsingleton (X ⧸ M) := rank_zero_iff.mp h_rank_zero
    have hM_top : M = ⊤ :=
      Submodule.Quotient.subsingleton_iff.mp h_subsingleton
    rw [hM_top, deviationFromRestriction_top]
end SNumbers
