-- Prove2me | solution 1 for PermanentRollout.freeAffineCircuit_homogeneousFiberDegree_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/5bf6335e-c594-48c5-8231-f21eafccc51a

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_affine_finrank_le_degree_product_of_weaklyRegular
import Theorems.Thm_PermanentRollout_affineTriangularInstructionOutputClosedFiber_finrank
import Theorems.Thm_PermanentRollout_freeAffineInstructionRhs_mem_gate_vars
import Theorems.Thm_PermanentRollout_freeAffineCircuitGraphEvaluation_extendedForm
import Theorems.Thm_PermanentRollout_freeAffineCircuitGate_eq_graphEvaluation_rhs
import Theorems.Thm_PermanentRollout_freeAffineCircuitSquareFamily_span_range
import Theorems.Thm_PermanentRollout_freeAffineCircuitSquareFamily_degree_product_le
import Theorems.Thm_PermanentRollout_freeAffineCircuitSquareFamily_isWeaklyRegular
import Theorems.Thm_PermanentRollout_freeAffineCircuitSquareFamily_zeroLocus_finite

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {k : ℕ} (circuit : FreeAffineCircuit (Fin k))
    (output : Fin k → FreeAffineForm (Fin k))
    (F : Fin k → MvPolynomial (Fin k) ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (target : Fin k → ℂ)
    (houtput : ∀ i, (output i).eval circuit.values = F i) :
    e ^ k ≤ 2 ^ circuit.multiplicationCount := by
  let rhs : Fin circuit.program.length →
      MvPolynomial (Fin k ⊕ Fin circuit.program.length) ℂ :=
    fun j => freeAffineInstructionRhs
      (n := circuit.program.length) (circuit.program.get j)
  let gate : Fin circuit.program.length → MvPolynomial (Fin k) ℂ :=
    freeAffineCircuitGate circuit
  let out : Fin k → MvPolynomial (Fin k ⊕ Fin circuit.program.length) ℂ :=
    fun i => freeAffineExtendedForm
      (n := circuit.program.length) (output i)
  have hgate : ∀ j, gate j = affineGateGraphEvaluation gate (rhs j) := by
    intro j
    simpa [gate, rhs, affineGateGraphEvaluation,
      freeAffineCircuitGraphEvaluation] using
      freeAffineCircuitGate_eq_graphEvaluation_rhs circuit j
  have htop : ∀ j i : Fin circuit.program.length,
      Sum.inr i ∈ (rhs j).vars → i.val < j.val := by
    intro j i hi
    exact freeAffineInstructionRhs_mem_gate_vars
      (circuit.program.get j) j (circuit.valid j) i hi
  have hout : ∀ i, affineGateGraphEvaluation gate (out i) = F i := by
    intro i
    simpa [gate, out, affineGateGraphEvaluation,
      freeAffineCircuitGraphEvaluation] using
      (freeAffineCircuitGraphEvaluation_extendedForm
        circuit (output i)).trans (houtput i)
  let f := freeAffineCircuitSquareFamily circuit output target
  have hweak := freeAffineCircuitSquareFamily_isWeaklyRegular
    circuit output F e he hF hzero target houtput
  have hfinite := freeAffineCircuitSquareFamily_zeroLocus_finite
    circuit output F e he hF hzero target houtput
  have hbezout := affine_finrank_le_degree_product_of_weaklyRegular
    f hweak hfinite
  rw [freeAffineCircuitSquareFamily_span_range] at hbezout
  have hfiber := affineTriangularInstructionOutputClosedFiber_finrank
    rhs gate out F e he hF hzero target hgate htop hout
  change
    Module.finrank ℂ
      (MvPolynomial (Fin k ⊕ Fin circuit.program.length) ℂ ⧸
        (affineTriangularInstructionIdeal rhs ⊔
          affineGateRawOutputIdeal out target)) = e ^ k at hfiber
  rw [hfiber] at hbezout
  exact hbezout.trans
    (freeAffineCircuitSquareFamily_degree_product_le
      circuit output target)
end PermanentRollout
