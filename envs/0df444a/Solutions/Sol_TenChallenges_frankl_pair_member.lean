-- Prove2me | solution 1 for TenChallenges.frankl_pair_member
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:35:14.4158+00:00
-- url     : https://prove2.me/submissions/531c957b-81f4-4731-80bb-b5dc41a48f83

import Definitions.Def_TenChallenges_Challenge_09
import Mathlib.Algebra.Order.Field.Rat

open Finset

/-- A union-closed family containing a pair has a half-dense element in that pair. -/
theorem solution {U : Type*} [DecidableEq U] (F : Finset (Finset U))
    (huc : IsUnionClosed F) {x y : U} (hxy : x ≠ y)
    (hpair : ({x, y} : Finset U) ∈ F) :
    (1 / 2 : ℚ) ≤ density F x ∨ (1 / 2 : ℚ) ≤ density F y := by
  classical
  have hinj : (F.filter fun A => x ∉ A ∧ y ∉ A).card ≤
      (F.filter fun A => x ∈ A ∧ y ∈ A).card := by
    refine card_le_card_of_injOn (fun A => ({x, y} : Finset U) ∪ A) ?_ ?_
    · exact fun A hA => mem_filter.mpr ⟨huc hpair (mem_filter.mp hA).1,
        by simp⟩
    · intro A hA B hB heq
      simpa [hxy, hxy.symm, (mem_filter.mp hA).2.1, (mem_filter.mp hA).2.2,
        (mem_filter.mp hB).2.1, (mem_filter.mp hB).2.2] using
        congrArg (fun S : Finset U => (S.erase x).erase y) heq
  have hsplit : (F.filter fun A => x ∈ A ∨ y ∈ A).card +
      (F.filter fun A => x ∉ A ∧ y ∉ A).card = F.card := by
    simpa only [not_or] using card_filter_add_card_filter_not
      (s := F) (fun A => x ∈ A ∨ y ∈ A)
  have hcount : occurrences F x + occurrences F y =
      (F.filter fun A => x ∈ A ∨ y ∈ A).card +
      (F.filter fun A => x ∈ A ∧ y ∈ A).card := by
    simpa [occurrences, ← filter_or, ← filter_and] using
      (card_union_add_card_inter (F.filter fun A => x ∈ A)
        (F.filter fun A => y ∈ A)).symm
  have hcard : F.card ≤ occurrences F x + occurrences F y := by omega
  have hpos : 1 ≤ F.card := card_pos.mpr ⟨{x, y}, hpair⟩
  have hposq : (0 : ℚ) < F.card := Nat.cast_pos.mpr hpos
  have hsum : (1 : ℚ) ≤ density F x + density F y := by
    simpa [density, max_eq_right hpos, ← add_div, le_div_iff₀ hposq] using
      (Nat.cast_le.mpr hcard : (F.card : ℚ) ≤ (occurrences F x + occurrences F y : ℕ))
  by_contra h
  exact (not_lt_of_ge hsum) ((add_lt_add
    (lt_of_not_ge (not_or.mp h).1) (lt_of_not_ge (not_or.mp h).2)).trans_eq
      (add_halves (1 : ℚ)))

#print axioms solution
