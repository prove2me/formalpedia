-- Prove2me | solution 1 for SNumbers.sn_le_approximationNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:56:44.770403+00:00
-- url     : https://prove2.me/submissions/00dccad3-7d7d-47ca-8caa-29f65ace7c98

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
public import Theorems.Thm_SNumbers_approximationSet_nonempty
public import Theorems.Thm_SNumbers_Additive_subadditive


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
theorem _root_.solution
    {s : Family 𝕜} (hs : IsSNumberSequence s) (S : X →L[𝕜] Y) (n : ℕ) :
    s S n ≤ approximationNumber S n := by
  refine le_csInf (approximationSet_nonempty S n) ?_
  rintro r ⟨A, hA, rfl⟩
  have hS_eq : S = A + (S - A) := by abel
  have h_low : s A n = 0 := hs.vanishes_on_low_rank A n hA
  calc s S n
      = s (A + (S - A)) n := by rw [← hS_eq]
    _ ≤ s A n + ‖S - A‖ := hs.subadditive A (S - A) n
    _ = ‖S - A‖ := by rw [h_low, zero_add]
end SNumbers
