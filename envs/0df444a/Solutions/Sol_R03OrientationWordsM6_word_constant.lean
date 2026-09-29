-- Prove2me | solution 1 for R03OrientationWordsM6.word_constant
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:34:53.221778+00:00
-- url     : https://prove2.me/submissions/f85f89a1-ec64-420f-b49a-c86236ba2044

import Mathlib.Data.Fintype.Pi
import Definitions.Def_r03_defs_67e8a31036_m6_OrientationWords

/- Candidate-only orientation-word algebra, NOT a graph or root theorem.
A nontrivial alternating component has k+1 virtual matching edges. A bit
chooses which adjacent ordinary edge receives its old center. Each ordinary
edge must receive exactly one center. k=0 includes a labelled parallel pair,
whose physical lift is a triangle. Common matching edges are not components.
The translation from graphs to this encoding requires separate review. -/
namespace R03OrientationWordsM6

theorem receive_one_iff (a b : Bool) : receive a b = 1 ↔ a = b := by
  cases a <;> cases b <;> decide


end R03OrientationWordsM6

open R03OrientationWordsM6
theorem solution (k : Nat) (f : Fin (k+1) → Bool) (h : Feasible k f) :
    ∀ i, f i = f 0 := by
  intro i
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => exact ((receive_one_iff _ _).mp (h.1 i)).symm.trans ih
