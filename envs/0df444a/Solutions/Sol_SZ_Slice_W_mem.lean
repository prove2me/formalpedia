-- Prove2me | solution 1 for SZ.Slice.W_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:28:38.483606+00:00
-- url     : https://prove2.me/submissions/e17cb09f-75f0-4bbc-9035-e7c2b270a31c

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_pick_adm
import Theorems.Thm_SZ_Slice_W_succ

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
variable {S}
namespace SZ.Slice
theorem _root_.solution {w₀ : ℝ} (h0 : 0 ≤ w₀) (h1 : w₀ ≤ (S.m : ℝ) * S.U) (k : ℕ) :
    0 ≤ S.W w₀ k ∧ S.W w₀ k ≤ (S.m : ℝ) * S.U := by
  induction k with
  | zero => exact ⟨h0, h1⟩
  | succ k ih =>
    obtain ⟨-, -, hlo, hhi⟩ := S.pick_adm ih.1 ih.2
    have hm : (0 : ℝ) ≤ (S.m : ℝ) := by positivity
    rw [W_succ]
    constructor
    · exact mul_nonneg hm hlo
    · exact mul_le_mul_of_nonneg_left hhi hm
end SZ.Slice
