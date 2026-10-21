-- Prove2me | solution 1 for VarStorageQN.LeastChange.bracket_comp
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:22:38.805425+00:00
-- url     : https://prove2.me/submissions/ac11ed74-8fa2-45c3-9cc9-1c706d63c137

import Mathlib
import Definitions.Def_VarStorageQN_LeastChange_HilbertSchmidt
import Definitions.Def_VarStorageQN_LeastChange_Bracket

set_option autoImplicit false
open InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace
open VarStorageQN.LeastChange

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem solution (R : H →L[ℝ] H) (u v : H) :
    R ∘L bracket u v = bracket (R u) v ∧
    bracket u v ∘L R = bracket u (adjoint R v) := by
  constructor
  · ext d
    simp [bracket, rankOne_apply]
  · ext d
    simp [bracket, rankOne_apply, adjoint_inner_left]
