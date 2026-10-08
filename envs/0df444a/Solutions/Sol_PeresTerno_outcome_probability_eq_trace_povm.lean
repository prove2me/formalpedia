-- Prove2me | solution 1 for PeresTerno.outcome_probability_eq_trace_povm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T01:00:57.906114+00:00
-- url     : https://prove2.me/submissions/ccd7bc7a-4e7c-48ee-8479-f41ee432ac77

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

set_option autoImplicit false

open Matrix
open scoped ComplexOrder

open Matrix PeresTerno in
theorem solution {d e ι : Type*} [Fintype d] [Fintype e] [Fintype ι]
    (A : ι → Matrix e d ℂ) (ρ : Matrix d d ℂ) :
    ∑ m, trace (A m * ρ * (A m)ᴴ) = trace (ρ * povmElement A) := by
  classical
  unfold povmElement
  rw [Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
