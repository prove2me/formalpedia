-- Prove2me | solution 1 for Planks.rot_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:37:55.0954+00:00
-- url     : https://prove2.me/submissions/9accf5fe-f4fe-41ee-98e8-a069655ad383

module
public import Mathlib
public import Definitions.Def_BallPlank_Planks

set_option autoImplicit true
@[expose] public section
public section
open scoped RealInnerProductSpace
open Classical
noncomputable section
open Planks
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι]
omit [FiniteDimensional ℝ E] [Fintype ι]
namespace Planks
theorem _root_.solution (y : ι → E) (i j : ι) : rot y i j 0 = y := by
  funext k
  by_cases hki : k = i
  · subst hki; simp [rot]
  · by_cases hkj : k = j
    · subst hkj; simp [rot, hki]
    · simp [rot, hki, hkj]
end Planks
