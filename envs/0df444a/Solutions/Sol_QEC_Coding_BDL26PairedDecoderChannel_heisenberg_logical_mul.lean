-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderChannel.heisenberg_logical_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:23:22.147062+00:00
-- url     : https://prove2.me/submissions/d6f6c8e3-cc25-4343-85a4-cf840fcd41a9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_pairEmbedding_mul
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_heisenberg_logical_algebra

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
theorem _root_.solution (A B : Operator Qubit.QubitSpace) :
    heisenberg S n (pairEmbedding (barePauliPair S n) A * pairEmbedding (barePauliPair S n) B) =
      heisenberg S n (pairEmbedding (barePauliPair S n) A) *
        heisenberg S n (pairEmbedding (barePauliPair S n) B) := by
  rw [← pairEmbedding_mul, heisenberg_logical_algebra, heisenberg_logical_algebra,
    heisenberg_logical_algebra, pairEmbedding_mul]
end QEC.Coding.BDL26PairedDecoderChannel
