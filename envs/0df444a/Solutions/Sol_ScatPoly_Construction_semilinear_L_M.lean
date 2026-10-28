-- Prove2me | solution 1 for ScatPoly.Construction.semilinear_L_M
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:28:45.362192+00:00
-- url     : https://prove2.me/submissions/8c59913e-3d56-4299-9b44-9328b05360a8

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model
import Definitions.Def_ScatPoly_Construction_Model

open ScatCaps.LinearSets ScatPoly.Construction in
theorem solution (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 3 ≤ t)
    (hcard : Fintype.card F = q ^ (2 * t))
    (h : F) (hh : h ^ (q ^ t + 1) = -1) :
    (∀ x y : F, Lmap q t h (x + y) = Lmap q t h x + Lmap q t h y) ∧
    (∀ x y : F, Mmap q t h (x + y) = Mmap q t h x + Mmap q t h y) ∧
    (∀ l ∈ subfieldOf F p r t, ∀ x : F, Lmap q t h (l * x) = l ^ q * Lmap q t h x) ∧
    (∀ l ∈ subfieldOf F p r t, ∀ x : F,
      Mmap q t h (l * x) = l ^ q ^ (t - 1) * Mmap q t h x) := by
  have hadd : ∀ k (x y : F), (x + y) ^ (q ^ k) = x ^ (q ^ k) + y ^ (q ^ k) := by
    intro k x y
    rw [hq, ← pow_mul]
    exact add_pow_char_pow x y p (r * k)
  have hadd1 : ∀ (x y : F), (x + y) ^ q = x ^ q + y ^ q := by
    intro x y
    have := hadd 1 x y
    simpa using this
  have hfix : ∀ l ∈ subfieldOf F p r t, l ^ (q ^ t) = l := by
    intro l hl
    have := RingHom.mem_eqLocusField.mp hl
    rw [iterateFrobenius_def] at this
    rw [hq, ← pow_mul]
    exact this
  refine ⟨fun x y => ?_, fun x y => ?_, fun l hl x => ?_, fun l hl x => ?_⟩
  · unfold Lmap
    rw [hadd1, hadd]
    ring
  · unfold Mmap
    rw [hadd, hadd]
    ring
  · unfold Lmap
    have hl1 : l ^ (q ^ (t + 1)) = l ^ q := by
      rw [pow_succ, pow_mul, hfix l hl]
    rw [mul_pow, mul_pow, hl1]
    ring
  · unfold Mmap
    have hl2 : l ^ (q ^ (2 * t - 1)) = l ^ (q ^ (t - 1)) := by
      have e : 2 * t - 1 = t + (t - 1) := by omega
      rw [e, pow_add, pow_mul, hfix l hl]
    rw [mul_pow, mul_pow, hl2]
    ring
