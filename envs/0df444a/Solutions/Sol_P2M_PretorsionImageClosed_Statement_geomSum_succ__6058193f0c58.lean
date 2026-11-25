-- Prove2me | solution 1 for P2M_PretorsionImageClosed_Statement_geomSum_succ__6058193f0c58
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:18:05.692328+00:00
-- url     : https://prove2.me/submissions/5325ba8e-b849-4e83-91d7-bee5eea7cb78

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open Polynomial
namespace PretorsionImageClosed.Statement
theorem _root_.solution (m : ℕ) : geomSum (m + 1) = X * geomSum m + U ^ (m + 1) := by
  unfold geomSum
  rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero, one_mul, Nat.sub_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have : m + 1 - (i + 1) = m - i := by omega
  rw [this, pow_succ]
  ring
end PretorsionImageClosed.Statement
