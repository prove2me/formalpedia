-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderChannel.source_even_readout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:24:02.836201+00:00
-- url     : https://prove2.me/submissions/b7637feb-6c1f-4179-afa4-62b9d024ff3a

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
theorem _root_.solution (k : Nat) (hk : 1 ≤ k) :
    ∃ n : Nat, n+2 = 2*k ∧ readout S n = (dressedPauliPair S n).thermalDecoding :=
  ⟨2*(k-1), BDL26TransposedStoppedDecoder.source_even_level k hk,
    readout_eq_dressed_decoder S _⟩
end QEC.Coding.BDL26PairedDecoderChannel
