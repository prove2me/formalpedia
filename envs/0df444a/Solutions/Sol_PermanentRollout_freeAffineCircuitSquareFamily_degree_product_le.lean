-- Prove2me | solution 1 for PermanentRollout.freeAffineCircuitSquareFamily_degree_product_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/23bbb2e9-bba9-4d83-9417-f35cb0568ea5

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_affine_output_equation_totalDegree_le_one
import Theorems.Thm_PermanentRollout_freeAffineExtendedForm_totalDegree_le_one
import Theorems.Thm_PermanentRollout_freeAffineCircuitInstructionEquation_degree_product_le
import Theorems.Thm_PermanentRollout_freeAffineCircuitSquareFamily_ofFn

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {k : ℕ} (circuit : FreeAffineCircuit (Fin k))
    (output : Fin k → FreeAffineForm (Fin k)) (target : Fin k → ℂ) :
    (∏ i,
      (freeAffineCircuitSquareFamily circuit output target i).totalDegree) ≤
      2 ^ circuit.multiplicationCount := by
  have hlist := congrArg
    (fun l : List
        (MvPolynomial (Fin k ⊕ Fin circuit.program.length) ℂ) =>
      (l.map (fun p => p.totalDegree)).prod)
    (freeAffineCircuitSquareFamily_ofFn circuit output target)
  have hproduct :
      (∏ i,
        (freeAffineCircuitSquareFamily circuit output target i).totalDegree) =
        (∏ j : Fin circuit.program.length,
          (freeAffineCircuitInstructionEquation circuit j).totalDegree) *
        (∏ i : Fin k,
          (freeAffineExtendedForm
            (n := circuit.program.length) (output i) -
              MvPolynomial.C (target i)).totalDegree) := by
    simpa only [List.map_append, List.prod_append,
      List.map_ofFn, Fin.prod_ofFn, Function.comp_apply] using hlist
  rw [hproduct]
  calc
    (∏ j : Fin circuit.program.length,
      (freeAffineCircuitInstructionEquation circuit j).totalDegree) *
      (∏ i : Fin k,
        (freeAffineExtendedForm
          (n := circuit.program.length) (output i) -
          MvPolynomial.C (target i)).totalDegree) ≤
        2 ^ circuit.multiplicationCount * 1 := by
          apply Nat.mul_le_mul
          · exact freeAffineCircuitInstructionEquation_degree_product_le circuit
          · calc
              (∏ i : Fin k,
                (freeAffineExtendedForm
                  (n := circuit.program.length) (output i) -
                  MvPolynomial.C (target i)).totalDegree) ≤
                    ∏ _ : Fin k, (1 : ℕ) := by
                      apply Finset.prod_le_prod'
                      intro i _
                      exact affine_output_equation_totalDegree_le_one
                        (freeAffineExtendedForm
                          (n := circuit.program.length) (output i))
                        (target i)
                        (freeAffineExtendedForm_totalDegree_le_one
                          (n := circuit.program.length) (output i))
              _ = 1 := by simp
    _ = 2 ^ circuit.multiplicationCount := Nat.mul_one _
end PermanentRollout
