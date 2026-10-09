-- Prove2me | solution 1 for Octonion.star_mul
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-23T13:33:33.436243+00:00
-- url     : https://prove2.me/submissions/f0e87719-10ed-4b70-a315-5b318fb722db

import Definitions.Def_Octonion_octonions
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

open Quaternion

namespace Octonion
variable {R : Type*} [CommRing R]

end Octonion

open Octonion
variable {R : Type*} [CommRing R]
/-- Conjugation reverses the Cayley-Dickson product: `(x * y)‾ = ȳ * x̄`. -/
theorem solution (x y : octonions R) : star (x * y) = star y * star x := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  show Octonion.conj (⟨a, b⟩ * ⟨c, d⟩) = Octonion.conj ⟨c, d⟩ * Octonion.conj ⟨a, b⟩
  ext <;> simp [Octonion.fst_mul, Octonion.snd_mul, Octonion.fst_conj, Octonion.snd_conj]

namespace Octonion


end Octonion
