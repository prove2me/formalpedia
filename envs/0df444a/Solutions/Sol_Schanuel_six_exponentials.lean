-- Prove2me | solution 1 for Schanuel.six_exponentials
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T12:32:51.298167+00:00
-- url     : https://prove2.me/submissions/f807df4c-d44f-4bb4-9eba-9ef6167f6748

import Mathlib
import Theorems.Thm_DiazModulus_six_exponentials

-- The statement is word for word `DiazModulus.six_exponentials`, Proved on this platform
-- (Lang–Ramachandra's six exponentials theorem, formalised in the Diaz mission).
theorem solution (x : Fin 2 → ℂ) (y : Fin 3 → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y) :
    ∃ i j, Transcendental ℚ (Complex.exp (x i * y j)) :=
  DiazModulus.six_exponentials x y hx hy

#print axioms solution
