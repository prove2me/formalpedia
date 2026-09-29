-- Prove2me | solution 1 for ThornStringBits.trace_prod_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T21:25:04.181989+00:00
-- url     : https://prove2.me/submissions/c7b5e306-af4a-4783-902c-8760333fd183

import Mathlib

set_option autoImplicit false

open Real Matrix

theorem solution {R : Type*} [CommRing R] {N M : ℕ}
    (a : Fin (M + 1) → Matrix (Fin N) (Fin N) R) :
    (List.ofFn a).prod.trace = ((List.ofFn a).rotate 1).prod.trace := by
  rw [List.ofFn_succ, List.rotate_cons_succ, List.rotate_zero, List.prod_cons, List.prod_append,
    List.prod_singleton, Matrix.trace_mul_comm]
