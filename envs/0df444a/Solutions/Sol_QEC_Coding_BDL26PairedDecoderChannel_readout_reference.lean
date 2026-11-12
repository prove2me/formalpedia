-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderChannel.readout_reference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:23:47.581175+00:00
-- url     : https://prove2.me/submissions/07eccd6d-2695-42ed-a2c3-1790a8b79eda

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_readout_eq_dressed_decoder

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
theorem _root_.solution (r : Nat) (A : OperatorMatrix r (Register S n)) :
    OperatorMatrix.map (readout S n).toLinearMap A =
      OperatorMatrix.map (dressedPauliPair S n).thermalDecoding.toLinearMap A := by
  rw [readout_eq_dressed_decoder]
end QEC.Coding.BDL26PairedDecoderChannel
