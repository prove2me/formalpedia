-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderGibbs.hamiltonian_mul_channel
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-11T15:21:57.690951+00:00
-- url     : https://prove2.me/submissions/00c0a4c8-9b21-4ad3-aa8b-be8e2ed9abee

import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_channel_left_support
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_hamiltonian_mul_ground
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
    hamiltonian S (n+2) * channel S n A = (groundEnergy S n : ℂ) • channel S n A := by
  calc
    _ = hamiltonian S (n+2) * (groundProjector S n * channel S n A) := by rw [channel_left_support]
    _ = _ := by rw [← mul_assoc, hamiltonian_mul_ground, smul_mul_assoc, channel_left_support]
