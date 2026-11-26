-- Prove2me | solution 1 for QuarterSumLadder.pm_gi_pow_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:55:36.701799+00:00
-- url     : https://prove2.me/submissions/cbbc8dcf-e19e-4ce3-964c-672357baaeb9

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_sq
attribute [local simp] QuarterSumLadder.gi_re
attribute [local simp] QuarterSumLadder.gi_im

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
namespace QuarterSumLadder
theorem _root_.solution {u : GaussianInt} (hu : u = gi ∨ u = -gi) {e : ℕ} (he : Odd e) :
    u ^ e = gi ∨ u ^ e = -gi := by
  obtain ⟨j, rfl⟩ := he
  have hu2 : u ^ 2 = -1 := by rcases hu with rfl | rfl <;> simp [gi_sq]
  rw [pow_succ, pow_mul, hu2]
  rcases neg_one_pow_eq_or GaussianInt j with h | h <;> rw [h] <;> rcases hu with rfl | rfl <;>
    simp
end QuarterSumLadder
