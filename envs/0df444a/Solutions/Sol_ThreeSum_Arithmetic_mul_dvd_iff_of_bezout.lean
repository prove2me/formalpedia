-- Prove2me | solution 1 for ThreeSum.Arithmetic.mul_dvd_iff_of_bezout
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:36:18.990948+00:00
-- url     : https://prove2.me/submissions/34037ca3-12a3-4376-8fe0-f16356940ca9

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Exact arithmetic interface for the deterministic histogram construction

These are finite arithmetic and counting theorems.  They do not assert a
running-time bound or the existence of a word-RAM implementation.
-/

namespace ThreeSum.Arithmetic

open Finset
open scoped BigOperators

/-! ## Guarded arithmetic-to-radix lifts -/






















































































































/-! ## The weighted false-count identity -/

/-- A concrete Bezout witness is enough for the product-divisibility
identity.  The statement does not assume primality or that the arithmetic
modulus is prime. -/
theorem mul_dvd_iff_of_bezout_sourceProof {m l x : ℤ}
    (hbez : ∃ u v : ℤ, u * m + v * l = 1) :
    m * l ∣ x ↔ m ∣ x ∧ l ∣ x := by
  constructor
  · rintro ⟨z, hz⟩
    constructor
    · refine ⟨l * z, ?_⟩
      rw [hz]
      ring
    · refine ⟨m * z, ?_⟩
      rw [hz]
      ring
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    obtain ⟨u, v, huv⟩ := hbez
    refine ⟨u * b + v * a, ?_⟩
    calc
      x = (u * m + v * l) * x := by rw [huv]; ring
      _ = u * m * x + v * l * x := by ring
      _ = u * m * (l * b) + v * l * (m * a) := by rw [← hb, ← ha]
      _ = m * l * (u * b + v * a) := by ring























































































































/-! ## Exact early YES from per-original-triple representation caps -/



































































end ThreeSum.Arithmetic

end


theorem solution : ∀ {m l x : Int},
  (∃ (u : Int) (v : Int),
      @Eq.{1} Int
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) u m)
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) v l))
        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))) →
    Iff (@Dvd.dvd.{0} Int Int.instDvd (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) m l) x)
      (And (@Dvd.dvd.{0} Int Int.instDvd m x) (@Dvd.dvd.{0} Int Int.instDvd l x)) := by
  exact @ThreeSum.Arithmetic.mul_dvd_iff_of_bezout_sourceProof

#print axioms solution
