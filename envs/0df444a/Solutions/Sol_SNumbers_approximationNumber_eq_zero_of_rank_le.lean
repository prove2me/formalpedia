-- Prove2me | solution 1 for SNumbers.approximationNumber_eq_zero_of_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:30:44.555235+00:00
-- url     : https://prove2.me/submissions/67d8f03e-fc9d-4a9f-8aa5-944e810b1e21

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
public import Theorems.Thm_SNumbers_bddBelow_approximationSet
public import Theorems.Thm_SNumbers_approximationNumber_nonneg
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_ContinuousLinearMap_rank_zero
attribute [local simp] ContinuousLinearMap.rank_zero


attribute [local simp] SNumbers.approximationNumber_zero_eq_norm

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
theorem _root_.solution {S : X →L[𝕜] Y} {n : ℕ}
    (hS : S.rank ≤ (n : Cardinal)) :
    approximationNumber S n = 0 := by
  refine le_antisymm ?_ (approximationNumber_nonneg S n)
  -- `0 = ‖S - S‖ ∈ approximationSet S n`, hence the infimum is `≤ 0`.
  have h0 : (0 : ℝ) ∈ approximationSet S n := ⟨S, hS, by simp⟩
  exact csInf_le (bddBelow_approximationSet S n) h0
end SNumbers
