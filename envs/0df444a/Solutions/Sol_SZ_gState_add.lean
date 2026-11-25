-- Prove2me | solution 1 for SZ.gState_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:36:29.397858+00:00
-- url     : https://prove2.me/submissions/82cbe3ec-913e-43e7-8791-d4762d19dd16

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_gState_succ

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (s : ℤ × ℤ) (N k : ℕ) : gState s (N + k) = gState (gState s N) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : N + (k + 1) = (N + k) + 1 := by omega
    rw [e, gState_succ, gState_succ]
    simp only [gDigit, ih]
end SZ
