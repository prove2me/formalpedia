-- Prove2me | solution 1 for PauliUnclonable531.Pauli.quadratic_sum
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T10:14:32.167841+00:00
-- url     : https://prove2.me/submissions/b4e5841d-27d6-4bc9-ac6d-9787c0abbf89

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Correlations
import Theorems.Thm_PauliUnclonable531_Pauli_quadratic_sandwich

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

open PauliUnclonable531.Pauli in
theorem solution {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    [Nonempty B] [Nonempty C] (n : ℕ) (hn : 1 ≤ n) (a : Decoders n B C) (t : ℝ) (ht : 0 < t) :
    Below ((EB a + EC a) * filterOperator a t * (EB a + EC a))
      ((2 * (t : ℂ)) • disagreement a +
        (2 : ℂ) • (EB a * filterOperator a t * EC a) +
        (2 : ℂ) • (EC a * filterOperator a t * EB a)) := by
  have h := quadratic_sandwich n hn a t ht
  unfold Below at h ⊢
  convert h using 1
  simp only [two_smul]
  noncomm_ring
