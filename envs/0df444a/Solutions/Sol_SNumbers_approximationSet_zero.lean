-- Prove2me | solution 1 for SNumbers.approximationSet_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:27:14.607341+00:00
-- url     : https://prove2.me/submissions/68c26d84-ff43-4804-861f-27e256b019fc

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
public import Theorems.Thm_ContinuousLinearMap_eq_zero_of_rank_le_zero
public import Theorems.Thm_ContinuousLinearMap_rank_zero
attribute [local simp] ContinuousLinearMap.rank_zero



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
    approximationSet S 0 = {‖S‖} := by
  ext r; constructor
  · rintro ⟨L, hL, rfl⟩
    have : L = 0 := ContinuousLinearMap.eq_zero_of_rank_le_zero (by exact_mod_cast hL)
    simp [this]
  · rintro rfl
    exact ⟨0, by simp, by simp⟩
end SNumbers
