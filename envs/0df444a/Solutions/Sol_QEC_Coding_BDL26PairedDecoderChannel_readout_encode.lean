-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderChannel.readout_encode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:00:39.797488+00:00
-- url     : https://prove2.me/submissions/47a2946e-371c-446d-a0a7-3fa96d4d2d15

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_readout_eq_dressed_decoder
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_thermalDecoding_thermalEncoding


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderChannel
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26PairedDecoderChannel._p2m_local_instance_c895a38b5b_28
attribute [local instance] QEC.Coding.BDL26PairedDecoderChannel._p2m_local_instance_c895a38b5b_29
namespace QEC.Coding.BDL26PairedDecoderChannel
theorem _root_.solution (sigma : DensityOperator (dressedPauliPair S n).AuxiliarySpace)
    (A : Operator Qubit.QubitSpace) :
    readout S n ((dressedPauliPair S n).thermalEncoding sigma A) = A := by
  rw [readout_eq_dressed_decoder]
  exact (dressedPauliPair S n).thermalDecoding_thermalEncoding sigma A
end QEC.Coding.BDL26PairedDecoderChannel
