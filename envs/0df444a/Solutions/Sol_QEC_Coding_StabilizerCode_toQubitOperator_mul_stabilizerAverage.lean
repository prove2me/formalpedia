-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.toQubitOperator_mul_stabilizerAverage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:28:39.236977+00:00
-- url     : https://prove2.me/submissions/29b682e9-c884-428f-bc6f-6c61eb0a2121

import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_binaryMul


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
universe u
open QEC.Coding.StabilizerCode
open PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.StabilizerCode
theorem _root_.solution
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    (S : Q.GeneratedGroupElement) :
    toQubitOperator S.1 * Q.stabilizerAverage = Q.stabilizerAverage := by
  rw [stabilizerAverage, Finset.mul_sum]
  simp_rw [← toQubitOperator_binaryMul]
  change (∑ P : Q.GeneratedGroupElement, toQubitOperator (S * P).1) =
    ∑ P : Q.GeneratedGroupElement, toQubitOperator P.1
  exact Equiv.sum_comp (Equiv.mulLeft S) (fun P => toQubitOperator P.1)
end QEC.Coding.StabilizerCode
