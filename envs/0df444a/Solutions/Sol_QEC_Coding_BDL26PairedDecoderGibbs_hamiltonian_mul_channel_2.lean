-- Prove2me | solution 2 for QEC.Coding.BDL26PairedDecoderGibbs.hamiltonian_mul_channel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:02:12.4245+00:00
-- url     : https://prove2.me/submissions/b632a816-c215-4ded-a123-2c7b7dd6464d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_channel_left_support
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_hamiltonian_mul_ground

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderGibbs
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_23
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_24
namespace QEC.Coding.BDL26PairedDecoderGibbs
theorem _root_.solution (A : Op S n) :
    hamiltonian S (n+2) * channel S n A = (groundEnergy S n : ℂ) • channel S n A := by
  calc
    _ = hamiltonian S (n+2) * (groundProjector S n * channel S n A) := by rw [channel_left_support]
    _ = _ := by rw [← mul_assoc, hamiltonian_mul_ground, smul_mul_assoc, channel_left_support]
end QEC.Coding.BDL26PairedDecoderGibbs
