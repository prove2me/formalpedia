-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CircuitProof.acceptance_complement_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:51:01.462802+00:00
-- url     : https://prove2.me/submissions/d27417ba-a2b7-4719-b7f6-b58849b27e9f

/- Generated from Solutions.CircuitUnitary by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates



open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.CircuitProof
end QMAPerfectCompleteness.Main.CircuitProof
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CircuitProof



















theorem QMAPerfectCompleteness.Main.CircuitProof.verifier_unitary {G : GateSet} (V : Verifier G) :
    V.unitary ∈ Matrix.unitaryGroup V.Wire ℂ := circuit_unitary V.gates

theorem QMAPerfectCompleteness.Main.CircuitProof.initialState_injective {G : GateSet} (V : Verifier G) :
    Function.Injective V.initialState := by
  intro p q hpq
  funext j
  have h := congrFun hpq (Fin.castAdd V.ancillaQubits j)
  simpa [Verifier.initialState] using h

/-- Initialization of the ancillas in zero is an isometry. -/
theorem QMAPerfectCompleteness.Main.CircuitProof.ancillaZero_isometry {G : GateSet} (V : Verifier G) :
    V.ancillaZeroᴴ * V.ancillaZero = 1 := by
  classical
  ext p q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Verifier.ancillaZero, Matrix.of_apply,
    apply_ite, star_one, star_zero, Matrix.one_apply]
  rw [Finset.sum_eq_single (V.initialState p)]
  · simp [initialState_injective V |>.eq_iff, eq_comm]
  · intro w _ hw
    simp [hw]
  · simp

open scoped ComplexOrder

/-- The complementary acceptance effect is positive, so all acceptance eigenvalues are ≤ 1. -/
theorem solution {G : GateSet} (V : Verifier G) :
    (1 - V.acceptanceOperator).PosSemidef := by
  have hp : (1 - V.acceptProjector).PosSemidef := by
    have heq : 1 - V.acceptProjector =
        Matrix.diagonal (fun w : V.Wire => if w V.output then (0 : ℂ) else 1) := by
      ext y x
      by_cases hyx : y = x
      · subst x
        cases hy : y V.output <;> simp [Verifier.acceptProjector, hy]
      · simp [Verifier.acceptProjector, hyx]
    rw [heq]
    apply Matrix.PosSemidef.diagonal
    intro w
    change 0 ≤ (if w V.output then (0 : ℂ) else 1)
    split <;> simp
  have hu : V.unitaryᴴ * V.unitary = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (verifier_unitary V)
  have hj := ancillaZero_isometry V
  have hgram : (V.unitary * V.ancillaZero)ᴴ * (V.unitary * V.ancillaZero) = 1 := by
    calc
      _ = V.ancillaZeroᴴ * (V.unitaryᴴ * V.unitary) * V.ancillaZero := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hu, Matrix.mul_one]; exact hj
  have heq : (V.unitary * V.ancillaZero)ᴴ * V.acceptProjector *
      (V.unitary * V.ancillaZero) = V.acceptanceOperator := by
    simp only [Verifier.acceptanceOperator, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hc := hp.conjTranspose_mul_mul_same (V.unitary * V.ancillaZero)
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hgram, heq] using hc
