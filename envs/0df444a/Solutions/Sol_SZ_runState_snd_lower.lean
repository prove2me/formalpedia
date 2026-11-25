-- Prove2me | solution 1 for SZ.runState_snd_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:28:11.102156+00:00
-- url     : https://prove2.me/submissions/4047ebf2-e5fc-4509-8df4-d5d631689e5b

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_runState_succ

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) (k : ℕ) :
    3 ^ k * (s₀.2 - 3) + 3 ≤ (runState s₀ d k).2 := by
  induction k with
  | zero => simp [runState]
  | succ k ih =>
    have hb : (d k).2 ≤ 2 := by rcases (hrun k).1.2 with h | h <;> omega
    have h3 : (3 : ℤ) ^ (k + 1) * (s₀.2 - 3) = 3 * (3 ^ k * (s₀.2 - 3)) := by ring
    rw [runState_succ, stepS]
    simp only
    rw [h3]
    linarith
end SZ
