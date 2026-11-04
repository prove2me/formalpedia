-- Prove2me | solution 1 for ThreeSum.Arithmetic.mul_dvd_iff_of_bezout_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:59.130934+00:00
-- url     : https://prove2.me/submissions/7e302a84-7e23-46a2-a69b-2af59ab62c3f

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Arithmetic

set_option autoImplicit false
open ThreeSum ThreeSum.Arithmetic
open Finset
open scoped BigOperators
namespace ThreeSum.Arithmetic
theorem _root_.solution {m l x : ℤ}
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
end ThreeSum.Arithmetic
