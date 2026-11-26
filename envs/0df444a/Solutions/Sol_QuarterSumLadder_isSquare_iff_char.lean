-- Prove2me | solution 1 for QuarterSumLadder.isSquare_iff_char
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:57:04.626847+00:00
-- url     : https://prove2.me/submissions/69337de2-582e-4f6f-b011-3ffe598962ba

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_sq
public import Theorems.Thm_QuarterSumLadder_pm_gi_pow_odd
public import Theorems.Thm_QuarterSumLadder_exists_generator
public import Theorems.Thm_QuarterSumLadder_quartic_values
public import Theorems.Thm_QuarterSumLadder_quartic_apply_generator
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
theorem _root_.solution {x : ZMod p} (hx : x ≠ 0) : IsSquare x ↔ (χ x = 1 ∨ χ x = -1) := by
  constructor
  · rintro ⟨m, rfl⟩
    have hm : m ≠ 0 := by rintro rfl; simp at hx
    rw [map_mul]
    rcases quartic_values χ hχ hm with h | h | h | h <;> rw [h]
    · left; ring
    · right; rw [← sq, gi_sq]
    · left; ring
    · right; rw [neg_mul_neg, ← sq, gi_sq]
  · intro h
    obtain ⟨g, -, hg⟩ := exists_generator (p := p)
    obtain ⟨j, hj⟩ := hg (Units.mk0 x hx)
    have hxj : x = (g : ZMod p) ^ j := by
      have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hj
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0] at this
      exact this.symm
    rcases Nat.even_or_odd j with ⟨i, rfl⟩ | hoddj
    · exact ⟨(g : ZMod p) ^ i, by rw [hxj, pow_add]⟩
    · exfalso
      have h' := pm_gi_pow_odd (quartic_apply_generator χ hχ hg) hoddj
      rw [← map_pow, ← hxj] at h'
      rcases h with h | h <;> rcases h' with h' | h' <;> rw [h] at h' <;> revert h' <;> decide
end QuarterSumLadder
