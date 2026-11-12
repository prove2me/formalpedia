-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.source_even_storage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:11:24.537792+00:00
-- url     : https://prove2.me/submissions/58f64075-9485-4d69-b5a5-05434c434e20

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_physical_storage

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalDefectStorage
open Classical Semantics BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26LogicalDefectStorage._p2m_local_instance_444300d501_96
attribute [local instance] QEC.Coding.BDL26LogicalDefectStorage._p2m_local_instance_444300d501_97
namespace QEC.Coding.BDL26LogicalDefectStorage
theorem _root_.solution (rates : ∀ j, Rate S j) (beta hmax : ℝ)
    (hb : 0 < beta) (hm : 0 < hmax)
    (hr : ∀ j qa omega, 0 < rates j qa omega ∧ rates j qa omega ≤ hmax)
    (hDB : ∀ j qa omega, rates j qa (BDL26BoundedRateDavies.oppositeFrequency S (j+2) omega) =
      Real.exp (-beta * omega.val) * rates j qa omega)
    (k : Nat) (hk : 1 ≤ k) :
    ∃ j : Nat, j+2 = 2*k ∧ ∀ (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t),
      (encodedError S j (rates j) beta eta t ht ≤ 8*t*g S j (rates j)*mass S j beta ∧
       decodedError S j (rates j) beta eta t ht ≤ 8*t*g S j (rates j)*mass S j beta) ∧
      (encodedError S j (rates j) beta eta t ht ≤ 48*t*qubits S j*hmax*mass S j beta ∧
       decodedError S j (rates j) beta eta t ht ≤ 48*t*qubits S j*hmax*mass S j beta) := by
  refine ⟨2*(k-1), BDL26TransposedStoppedDecoder.source_even_level k hk, ?_⟩
  intro eta t ht
  exact physical_storage S _ (rates _) beta hmax hb hm (hr _) (hDB _) eta t ht
end QEC.Coding.BDL26LogicalDefectStorage
