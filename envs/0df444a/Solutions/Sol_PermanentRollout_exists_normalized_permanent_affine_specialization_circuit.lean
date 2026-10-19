-- Prove2me | solution 1 for PermanentRollout.exists_normalized_permanent_affine_specialization_circuit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/409b0d5f-3020-4214-8a1a-3a045c0a2c60

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_FreeAffineForm_eval_substituteInputs
import Theorems.Thm_PermanentRollout_FreeAffineInstruction_eval_substituteInputs
import Theorems.Thm_PermanentRollout_FreeAffineCircuit_values_substituteInputs
import Theorems.Thm_PermanentRollout_FreeAffineCircuit_multiplicationCount_ofArithmetic_le

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {n m : ℕ}
    (circuit : ArithmeticCircuit (Fin n × Fin n))
    (hpermanent : circuit.polynomial = permanent n)
    (substitution : (Fin n × Fin n) → FreeAffineInput (Fin m))
    (P : MvPolynomial (Fin m) ℂ)
    (c : ℂ) (hc : c ≠ 0)
    (hspecialization :
      MvPolynomial.aeval (fun ij => (substitution ij).polynomial)
          (permanent n) = MvPolynomial.C c * P) :
    ∃ D : FreeAffineCircuit (Fin m),
      ∃ output : FreeAffineForm (Fin m),
        output ∈ D.outputs ∧
        output.eval D.values = P ∧
        D.multiplicationCount ≤ circuit.size := by
  classical
  let free := FreeAffineCircuit.ofArithmetic circuit
  let base := free.substituteInputs substitution
  let raw : FreeAffineForm (Fin m) :=
    (FreeAffineForm.gate circuit.output).substituteInputs substitution
  let output : FreeAffineForm (Fin m) := c⁻¹ • raw
  have hraw : raw ∈ base.outputs := by
    simp [base, free, raw, FreeAffineCircuit.substituteInputs,
      FreeAffineCircuit.ofArithmetic]
  have hvalid : ∀ form ∈ ([output] : List (FreeAffineForm (Fin m))),
      ∀ index : ℕ,
        form.gateCoefficients index ≠ 0 → index < base.program.length := by
    intro form hform index hindex
    have heq : form = output := List.mem_singleton.mp hform
    subst form
    have hrawne : raw.gateCoefficients index ≠ 0 := by
      intro hz
      apply hindex
      change ((c⁻¹ • raw.gateCoefficients : ℕ →₀ ℂ) index) = 0
      simp [hz]
    exact base.validOutputs raw hraw index hrawne
  let D := base.withOutputs [output] hvalid
  refine ⟨D, output, by simp [D, FreeAffineCircuit.withOutputs], ?_, ?_⟩
  · change output.eval base.values = P
    change (c⁻¹ • raw).eval base.values = P
    rw [FreeAffineForm.eval_smul]
    have hrawvalue : raw.eval base.values =
        MvPolynomial.aeval (fun ij => (substitution ij).polynomial)
          (permanent n) := by
      dsimp [raw, base]
      rw [FreeAffineCircuit.values_substituteInputs,
        FreeAffineForm.eval_substituteInputs,
        FreeAffineForm.eval_gate,
        FreeAffineCircuit.values_ofArithmetic]
      change MvPolynomial.aeval (fun ij => (substitution ij).polynomial)
        circuit.polynomial = _
      rw [hpermanent]
      apply DFunLike.congr_fun (x := permanent n)
      apply MvPolynomial.algHom_ext
      intro ij
      simp
    rw [hrawvalue, hspecialization]
    rw [MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ hc, map_one, one_mul]
  · change base.multiplicationCount ≤ circuit.size
    dsimp [base, free]
    rw [FreeAffineCircuit.multiplicationCount_substituteInputs]
    exact FreeAffineCircuit.multiplicationCount_ofArithmetic_le circuit
end PermanentRollout
