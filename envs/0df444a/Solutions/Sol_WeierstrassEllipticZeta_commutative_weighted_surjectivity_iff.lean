-- Prove2me | solution 1 for WeierstrassEllipticZeta.commutative_weighted_surjectivity_iff
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-11T20:08:16.709574+00:00
-- url     : https://prove2.me/submissions/702b80f6-42cf-4807-8663-5c6b77c9837d

import Mathlib.Algebra.Group.Units.Basic



theorem solution
    (α M : Type*) [CommMonoid M] (f : α → M) (a : M) :
    Function.Surjective (fun s => f s * a) ↔ Function.Surjective f ∧ IsUnit a := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := h 1
    have ha : IsUnit a := isUnit_iff_exists_inv'.2 ⟨f s, hs⟩
    refine ⟨?_, ha⟩
    intro y
    obtain ⟨t, ht⟩ := h (y * a)
    exact ⟨t, ha.mul_right_cancel ht⟩
  · rintro ⟨hf, ha⟩
    exact (IsUnit.isUnit_iff_mulRight_bijective.mp ha).2.comp hf

