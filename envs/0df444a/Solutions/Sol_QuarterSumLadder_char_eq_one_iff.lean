-- Prove2me | solution 1 for QuarterSumLadder.char_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:02:22.270074+00:00
-- url     : https://prove2.me/submissions/2a3f14c8-2f83-4250-a291-9618a2ac036a

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_exists_generator
public import Theorems.Thm_QuarterSumLadder_quartic_values
public import Theorems.Thm_QuarterSumLadder_quartic_apply_generator
public import Theorems.Thm_QuarterSumLadder_gi_pow_eq_one_iff
attribute [local simp] QuarterSumLadder.gi_re
attribute [local simp] QuarterSumLadder.gi_im

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace QuarterSumLadder
theorem _root_.solution {n : ZMod p} (hn : n ≠ 0) : χ n = 1 ↔ ∃ y : ZMod p, y ^ 4 = n := by
  constructor
  · intro h
    obtain ⟨g, -, hg⟩ := exists_generator (p := p)
    obtain ⟨j, hj⟩ := hg (Units.mk0 n hn)
    have hnj : n = (g : ZMod p) ^ j := by
      have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hj
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0] at this
      exact this.symm
    rw [hnj, map_pow, gi_pow_eq_one_iff (quartic_apply_generator χ hχ hg)] at h
    obtain ⟨q, rfl⟩ := h
    exact ⟨(g : ZMod p) ^ q, by rw [hnj, ← pow_mul, mul_comm]⟩
  · rintro ⟨y, rfl⟩
    have hy : y ≠ 0 := by rintro rfl; exact hn (by simp)
    rw [map_pow]
    rcases quartic_values χ hχ hy with h | h | h | h <;> rw [h] <;> decide
end QuarterSumLadder
