-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectStorage.conditional_terminal_horizon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:12:58.416773+00:00
-- url     : https://prove2.me/submissions/0018c63a-a0f3-421d-8015-22d77aac7e09

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_conditional_terminal_bound

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
theorem _root_.solution (rate : Rate S n) (beta hmax : ℝ) (hm : 0 ≤ hmax)
    (hn : ∀ qa omega, 0 ≤ rate qa omega) (hu : ∀ qa omega, rate qa omega ≤ hmax)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (k : Nat) (hx : xMass S n beta ≤ 2*peierlsScale k) (hz : zMass S n beta ≤ 2*peierlsScale k)
    (hp : 0 < qubits S n * hmax * peierlsScale k)
    (eta : DensityOperator Qubit.QubitSpace) (delta t : ℝ) (_hd : 0 ≤ delta) (ht : 0 ≤ t)
    (hw : t ≤ delta / (192 * qubits S n * hmax * peierlsScale k)) :
    encodedError S n rate beta eta t ht ≤ delta ∧ decodedError S n rate beta eta t ht ≤ delta := by
  obtain ⟨he,hh⟩ := conditional_terminal_bound S n rate beta hmax hm hn hu hDB k hx hz eta t ht
  have hp' : 0 < 192 * qubits S n * hmax * peierlsScale k := by nlinarith
  have hw' := (le_div_iff₀ hp').mp hw
  constructor <;> nlinarith
end QEC.Coding.BDL26LogicalDefectStorage
