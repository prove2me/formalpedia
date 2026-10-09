-- Prove2me | solution 1 for Octonion.normSq_mul
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-23T13:32:01.501752+00:00
-- url     : https://prove2.me/submissions/1a139cb9-48a0-4354-a617-d6d8469a1a83

import Definitions.Def_Octonion_normSq
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
/-- The norm is multiplicative (the Hurwitz property): `N (x * y) = N x * N y`.
Proved over any commutative base ring by expanding both sides into eight coordinates
and closing with `ring`. This statement does not assert a division structure. -/
theorem solution (x y : octonions R) : Octonion.normSq (x * y) = Octonion.normSq x * Octonion.normSq y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  show Quaternion.normSq (((⟨a, b⟩ : octonions R) * ⟨c, d⟩).fst) +
      Quaternion.normSq (((⟨a, b⟩ : octonions R) * ⟨c, d⟩).snd) =
    (Quaternion.normSq a + Quaternion.normSq b) * (Quaternion.normSq c + Quaternion.normSq d)
  simp only [Octonion.fst_mul, Octonion.snd_mul, normSq_def', re_add, imI_add, imJ_add, imK_add, re_sub, imI_sub,
    imJ_sub, imK_sub, re_mul, imI_mul, imJ_mul, imK_mul,
    re_star, imI_star, imJ_star, imK_star]
  ring

namespace Octonion


end Octonion
