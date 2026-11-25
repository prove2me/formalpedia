-- Prove2me | solution 1 for SZ.runState_gDigit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:28:22.516332+00:00
-- url     : https://prove2.me/submissions/0cc60000-d078-4e40-8fa9-d1be3df53d74

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_runState_succ
import Theorems.Thm_SZ_gState_succ

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (s : ℤ × ℤ) (k : ℕ) : runState s (gDigit s) k = gState s k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [runState_succ, ih, gState_succ]
end SZ
