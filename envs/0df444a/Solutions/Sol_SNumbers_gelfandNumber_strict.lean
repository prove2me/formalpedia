-- Prove2me | solution 1 for SNumbers.gelfandNumber_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:26:43.765741+00:00
-- url     : https://prove2.me/submissions/173c2131-679b-4f18-86b9-f4aaaf58ea74

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
public import Theorems.Thm_SNumbers_gelfandSet_nonempty
public import Theorems.Thm_SNumbers_gelfandNumber_le_deviation
public import Theorems.Thm_SNumbers_ne_bot_of_rank_quotient_le_of_lt_rank
public import Theorems.Thm_SNumbers_nontrivial_of_natCast_lt_rank

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
theorem _root_.solution {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (n : ℕ) (h : (n : Cardinal) < Module.rank 𝕜 X) :
    gelfandNumber (ContinuousLinearMap.id 𝕜 X) n = 1 := by
  have : Nontrivial X := nontrivial_of_natCast_lt_rank h
  set I := ContinuousLinearMap.id 𝕜 X with hI_def
  refine le_antisymm ?_ ?_
  · -- `≤ 1`: take `M = ⊤`. `deviation(I, ⊤) = ‖I‖ = 1`.
    have h_rank_top : Module.rank 𝕜 (X ⧸ (⊤ : Submodule 𝕜 X)) ≤ (n : Cardinal) := by
      have h0 : Module.rank 𝕜 (X ⧸ (⊤ : Submodule 𝕜 X)) = 0 :=
        rank_zero_iff.mpr inferInstance
      rw [h0]; exact zero_le
    have h_closed : IsClosed ((⊤ : Submodule 𝕜 X) : Set X) := by
      rw [Submodule.top_coe]; exact isClosed_univ
    calc gelfandNumber I n
        ≤ deviationFromRestriction I ⊤ := gelfandNumber_le_deviation h_closed h_rank_top
      _ = ‖I‖ := deviationFromRestriction_top _
      _ = 1 := norm_id
  · -- `≥ 1`: every admissible `M` is non-trivial, so
    -- `‖I.comp M.subtypeL‖ = ‖M.subtypeL‖ = 1`.
    refine le_csInf (gelfandSet_nonempty I n) ?_
    rintro _ ⟨M, _, hM_rank, rfl⟩
    -- Show `Nontrivial M` from `codim M ≤ n < dim X`.
    have : Nontrivial M :=
      Submodule.nontrivial_iff_ne_bot.mpr (ne_bot_of_rank_quotient_le_of_lt_rank hM_rank h)
    -- `I.comp M.subtypeL = M.subtypeL`, and its norm is 1.
    have h_dev_eq : deviationFromRestriction I M = ‖M.subtypeL‖ := by
      show ‖I.comp M.subtypeL‖ = ‖M.subtypeL‖
      rw [hI_def, ContinuousLinearMap.id_comp]
    rw [h_dev_eq, M.norm_subtypeL]
end SNumbers
