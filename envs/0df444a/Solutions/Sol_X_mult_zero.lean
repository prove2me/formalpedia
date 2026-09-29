-- Prove2me | solution 1 for X_mult_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T06:30:58.611894+00:00
-- url     : https://prove2.me/submissions/43b8634b-50b5-47ae-ada8-5af54c4c35e6

import Mathlib
import Definitions.Def_timepiece_corrector
import Theorems.Thm_X_p_zero
open Complex Finset Filter Topology
open scoped ArithmeticFunction ArithmeticFunction.Moebius ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (n P : ℕ) : X_mult n P (fun _ ↦ 0) = 1 := by
  unfold X_mult
  have h : ∀ L : List ℕ, ((L.map (fun p ↦ X_p p P (fun _ ↦ 0))).prod) = 1 := by
    intro L
    induction L with
    | nil => rfl
    | cons p l ih =>
      rw [List.map_cons, List.prod_cons, X_p_zero, one_mul, ih]
  exact h (Nat.primeFactorsList n)
