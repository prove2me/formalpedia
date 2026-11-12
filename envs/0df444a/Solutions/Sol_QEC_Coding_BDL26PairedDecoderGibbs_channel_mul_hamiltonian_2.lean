-- Prove2me | solution 2 for QEC.Coding.BDL26PairedDecoderGibbs.channel_mul_hamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:02:26.02778+00:00
-- url     : https://prove2.me/submissions/bce70e20-31d8-4330-a3f6-b9f34dd877df

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_channel_right_support
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_ground_mul_hamiltonian

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
    channel S n A * hamiltonian S (n+2) = (groundEnergy S n : ℂ) • channel S n A := by
  calc
    _ = (channel S n A * groundProjector S n) * hamiltonian S (n+2) := by rw [channel_right_support]
    _ = _ := by rw [mul_assoc, ground_mul_hamiltonian, mul_smul_comm, channel_right_support]
end QEC.Coding.BDL26PairedDecoderGibbs
