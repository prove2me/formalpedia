-- Prove2me | solution 1 for SNumbers.hilbertNumber_eq_zero_of_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:05:35.635005+00:00
-- url     : https://prove2.me/submissions/f042394f-6aaa-4df4-abcb-c05b4b8acb27

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_Hilbert
public import Theorems.Thm_SNumbers_hilbertNumber_def
public import Theorems.Thm_SNumbers_hilbertNumber_nonneg
public import Theorems.Thm_ContinuousLinearMap_rank_comp_comp_le
public import Theorems.Thm_SNumbers_approximationNumber_eq_zero_of_rank_le


set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y W Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution {S : X →L[𝕜] Y} {n : ℕ}
    (hS : S.rank ≤ (n : Cardinal)) : hilbertNumber S n = 0 := by
  have hkey : ∀ (A : L2 𝕜 →L[𝕜] X) (B : Y →L[𝕜] L2 𝕜),
      approximationNumber (B.comp (S.comp A)) n = 0 := fun A B =>
    approximationNumber_eq_zero_of_rank_le
      ((ContinuousLinearMap.rank_comp_comp_le A S B).trans hS)
  rw [hilbertNumber_def]
  refine le_antisymm (Real.sSup_le ?_ le_rfl) (hilbertNumber_nonneg S n)
  rintro r ⟨A, B, _, _, rfl⟩
  rw [hkey A B, zero_div]
end SNumbers
