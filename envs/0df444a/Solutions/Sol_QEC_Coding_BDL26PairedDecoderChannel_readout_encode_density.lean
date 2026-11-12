-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderChannel.readout_encode_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:23:35.709202+00:00
-- url     : https://prove2.me/submissions/ca5befa7-e148-499f-94f2-31f4dd2be0f4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_readout_encode
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator


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
    (rho : DensityOperator Qubit.QubitSpace) :
    (readout S n).mapDensity ((dressedPauliPair S n).thermalEncoding sigma |>.mapDensity rho) = rho := by
  apply DensityOperator.ext_toOperator
  exact readout_encode S n sigma rho.toOperator
end QEC.Coding.BDL26PairedDecoderChannel
