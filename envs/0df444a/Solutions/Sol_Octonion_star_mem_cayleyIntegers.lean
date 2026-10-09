-- Prove2me | solution 1 for Octonion.star_mem_cayleyIntegers
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-23T13:33:31.601957+00:00
-- url     : https://prove2.me/submissions/b2451f57-09d4-45ae-ba44-eddcf52fb7b8

import Definitions.Def_Octonion_cayleyIntegers
import Definitions.Def_Octonion_octonions
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace Octonion

/-- Membership in the Cayley integers is exactly the lattice condition `isCayley`: all eight
coordinates lie in `½ℤ` and the parity pattern of the doubled coordinates is a Hamming codeword.
As a `simp` lemma this insulates users from the subring's set representation. -/
@[simp]
theorem mem_cayleyIntegers (x : octonions ℚ) :
    x ∈ cayleyIntegers ↔ isCayley x :=
  Iff.rfl

end Octonion

open Quaternion

namespace Octonion

end Octonion

open Octonion

/-- The Cayley integers are closed under octonion conjugation: `star` negates the imaginary
coordinates, and negation preserves parity, so the doubled coordinate vector keeps its Hamming
pattern. -/
theorem solution {x : octonions ℚ} (hx : x ∈ Octonion.cayleyIntegers) :
    star x ∈ Octonion.cayleyIntegers := by
  rw [Octonion.mem_cayleyIntegers] at hx ⊢
  obtain ⟨a, rfl, pa⟩ := hx
  refine ⟨fun i => if i = 0 then a i else -a i, ?_, ?_⟩
  · apply Octonion.ext_coord8
    intro i
    have hst : star (Octonion.halfOf a) = Octonion.conj (Octonion.halfOf a) := rfl
    rw [hst, Octonion.coord8_conj]
    by_cases h : i = 0
    · simp [h, Octonion.coord8_halfOf]
    · simp only [if_neg h, Octonion.coord8_halfOf]
      push_cast
      ring
  · obtain ⟨m, hm, ham⟩ := Finset.mem_image.mp pa
    refine Finset.mem_image.mpr ⟨m, hm, ?_⟩
    have key : (fun i => decide (Odd (if i = 0 then a i else -a i))) =
        fun i => decide (Odd (a i)) := by
      funext i
      by_cases hi : i = 0 <;> by_cases h : Odd (a i) <;> simp [hi, h]
    rw [key, ← ham]

namespace Octonion


end Octonion
