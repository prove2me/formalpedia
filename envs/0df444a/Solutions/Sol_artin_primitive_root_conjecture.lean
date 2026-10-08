-- Prove2me | solution 1 for artin_primitive_root_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T08:50:00.939921+00:00
-- url     : https://prove2.me/submissions/6d2d975f-64ab-4981-afa2-476723c44dc2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_ArtinPrimitiveRoots_primitive_root_primes_lower_bound

theorem solution (a : ℤ)
    (ha_ne_neg1 : a ≠ -1)
    (ha_not_sq : ¬∃ m : ℤ, a = m ^ 2) :
    {p : ℕ | Nat.Prime p ∧ orderOf (a : ZMod p) = p - 1}.Infinite := by
  have hsq : ¬ IsSquare a := by
    rintro ⟨m, rfl⟩; exact ha_not_sq ⟨m, by ring⟩
  obtain ⟨c, hc, x₀, hx₀, hbound⟩ :=
    ArtinPrimitiveRoots.primitive_root_primes_lower_bound a ha_ne_neg1 hsq
  intro hfin
  obtain ⟨B, hB⟩ := hfin.bddAbove
  set x : ℝ := max x₀ (B + 1) with hxdef
  have hx0 : x₀ ≤ x := le_max_left _ _
  have hxB : (B : ℝ) + 1 ≤ x := le_max_right _ _
  have hx2 : (2 : ℝ) ≤ x := le_trans hx₀ hx0
  have hempty : {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) < 2 * x ∧ ¬ (p : ℤ) ∣ a ∧
      orderOf (a : ZMod p) = p - 1} = ∅ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hp, hxp, -, -, hord⟩
    have : p ≤ B := hB ⟨hp, hord⟩
    have : (p : ℝ) ≤ B := by exact_mod_cast this
    linarith
  have h := hbound x hx0
  rw [hempty] at h
  simp only [Nat.card_of_isEmpty, Nat.cast_zero] at h
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have : 0 < c * x / Real.log x ^ 2 := by positivity
  linarith
