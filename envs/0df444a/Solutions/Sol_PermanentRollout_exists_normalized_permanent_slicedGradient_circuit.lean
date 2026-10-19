-- Prove2me | solution 1 for PermanentRollout.exists_normalized_permanent_slicedGradient_circuit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/5d5a8129-656f-4ec1-b736-0beca03190bf

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_exists_actual_slicedGradient_freeAffineCircuit
import Theorems.Thm_PermanentRollout_exists_normalized_permanent_affine_specialization_circuit

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {n m k : ℕ}
    (circuit : ArithmeticCircuit (Fin n × Fin n))
    (hpermanent : circuit.polynomial = permanent n)
    (substitution : (Fin n × Fin n) → FreeAffineInput (Fin m))
    (P : MvPolynomial (Fin m) ℂ)
    (c : ℂ) (hc : c ≠ 0)
    (hspecialization :
      MvPolynomial.aeval (fun ij => (substitution ij).polynomial)
          (permanent n) = MvPolynomial.C c * P)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ)) :
    ∃ D : FreeAffineCircuit (Fin k),
      D.multiplicationCount ≤ 3 * circuit.size ∧
      D.polynomials = (Finset.univ : Finset (Fin k)).toList.map
        (slicedGradientPolynomial P W A) := by
  obtain ⟨source, output, houtput, hvalue, hcount⟩ :=
    exists_normalized_permanent_affine_specialization_circuit
      circuit hpermanent substitution P c hc hspecialization
  obtain ⟨D, hDcount, hDpolynomials⟩ :=
    exists_actual_slicedGradient_freeAffineCircuit
      source output houtput W A
  refine ⟨D, ?_, ?_⟩
  · rw [hDcount]
    exact Nat.mul_le_mul_left 3 hcount
  · simpa [hvalue] using hDpolynomials
end PermanentRollout
