-- Prove2me | solution 1 for SNumbers.approximationNumber_additive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:27:43.649544+00:00
-- url     : https://prove2.me/submissions/45778cc9-b14c-4546-90c3-9d235788b3c0

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
public import Theorems.Thm_SNumbers_approximationSet_nonempty
public import Theorems.Thm_SNumbers_approximationNumber_add_le_norm_sub_add

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
theorem _root_.solution (S T : X →L[𝕜] Y) (n m : ℕ) :
    approximationNumber (S + T) (n + m) ≤
      approximationNumber S n + approximationNumber T m := by
  -- infimum over the approximants `L` of `S`
  rw [← sub_le_iff_le_add]
  refine le_csInf (approximationSet_nonempty S n) ?_
  rintro _ ⟨L, hL, rfl⟩
  -- infimum over the approximants `K` of `T`
  rw [sub_le_comm]
  refine le_csInf (approximationSet_nonempty T m) ?_
  rintro _ ⟨K, hK, rfl⟩
  linarith [approximationNumber_add_le_norm_sub_add (S := S) (T := T) hL hK]
end SNumbers
