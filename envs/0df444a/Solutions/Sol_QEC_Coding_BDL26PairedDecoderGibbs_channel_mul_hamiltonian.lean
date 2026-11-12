-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderGibbs.channel_mul_hamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-11T15:21:58.925861+00:00
-- url     : https://prove2.me/submissions/28aab687-7e2a-4cc3-85a8-13f3839a41f7

import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_channel_right_support
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_ground_mul_hamiltonian
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderGibbs
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_23
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_24
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_416

theorem solution (A : Op S n) :
    channel S n A * hamiltonian S (n+2) = (groundEnergy S n : ℂ) • channel S n A := by
  calc
    _ = (channel S n A * groundProjector S n) * hamiltonian S (n+2) := by rw [channel_right_support]
    _ = _ := by rw [mul_assoc, ground_mul_hamiltonian, mul_smul_comm, channel_right_support]
