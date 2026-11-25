-- Prove2me | solution 1 for SZ.runVal_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:14:50.877152+00:00
-- url     : https://prove2.me/submissions/6bd9f5fd-796b-40b0-af37-0b71818c8d34

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_valS_stepS
import Theorems.Thm_SZ_runState_succ

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d)
    (h0 : 0 ≤ valS s₀) (h1 : valS s₀ ≤ 3 + 3 * Real.sqrt 3) (k : ℕ) :
    0 ≤ valS (runState s₀ d k) ∧ valS (runState s₀ d k) ≤ 3 + 3 * Real.sqrt 3 := by
  induction k with
  | zero => exact ⟨h0, h1⟩
  | succ k ih =>
    obtain ⟨-, hlo, hhi⟩ := hrun k
    rw [runState_succ, valS_stepS]
    constructor <;> linarith
end SZ
