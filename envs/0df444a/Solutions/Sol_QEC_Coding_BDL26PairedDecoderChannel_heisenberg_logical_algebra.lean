-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderChannel.heisenberg_logical_algebra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:47:24.06389+00:00
-- url     : https://prove2.me/submissions/58b4fb5c-743b-4010-9016-99502c2f6c13

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_trace_duality
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_readout_eq_dressed_decoder_apply
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_partialTraceRightRaw_trace_pairing
import Theorems.Thm_QEC_Semantics_operator_ext_of_trace_comp_right_eq

section
noncomputable section
namespace QEC.Coding.BDL26PairedDecoderChannel
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
private theorem decoding_trace {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
    (P : ThermalEncoding.PauliLikePair H) (A : Operator H) (O : Operator Qubit.QubitSpace) :
    LinearMap.trace ℂ Qubit.QubitSpace (P.thermalDecoding A * O) =
      LinearMap.trace ℂ H (A * P.factorization.conjOperator
        (TensorProduct.map O (1 : Operator P.AuxiliarySpace))) := by
  change LinearMap.trace ℂ Qubit.QubitSpace
    (partialTraceRightRaw Qubit.QubitSpace P.AuxiliarySpace
      (P.factorization.symm.conjOperator A) * O) = _
  rw [show LinearMap.trace ℂ Qubit.QubitSpace
      (partialTraceRightRaw Qubit.QubitSpace P.AuxiliarySpace
        (P.factorization.symm.conjOperator A) * O) =
      LinearMap.trace ℂ (CompositeSystem Qubit.QubitSpace P.AuxiliarySpace)
        (P.factorization.symm.conjOperator A * TensorProduct.map O (1 : Operator P.AuxiliarySpace)) by
    exact FiniteMatrixEntropy.partialTraceRightRaw_trace_pairing
      (stdOrthonormalBasis ℂ P.AuxiliarySpace) _ _]
  rw [← P.factorization.trace_conjOperator,
    P.factorization.conjOperator_mul, P.factorization.conjOperator_symm_conjOperator]
end QEC.Coding.BDL26PairedDecoderChannel
end
end

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
theorem _root_.solution (O : Operator Qubit.QubitSpace) :
    heisenberg S n (pairEmbedding (barePauliPair S n) O) =
      pairEmbedding (dressedPauliPair S n) O := by
  apply Semantics.operator_ext_of_trace_comp_right_eq
  intro A
  change LinearMap.trace ℂ (Register S n)
      (A * heisenberg S n (pairEmbedding (barePauliPair S n) O)) = _
  calc
    _ = LinearMap.trace ℂ (Register S n)
        (channel S n A * pairEmbedding (barePauliPair S n) O) :=
      (trace_duality S n A _).symm
    _ = LinearMap.trace ℂ Qubit.QubitSpace (readout S n A * O) :=
      (decoding_trace (barePauliPair S n) (channel S n A) O).symm
    _ = LinearMap.trace ℂ (Register S n)
        (A * pairEmbedding (dressedPauliPair S n) O) := by
      rw [readout_eq_dressed_decoder_apply]
      exact decoding_trace (dressedPauliPair S n) A O
end QEC.Coding.BDL26PairedDecoderChannel
