-- Prove2me | solution 2 for QEC.Coding.BDL26PairedDecoderGibbs.encoding_Y
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:04:26.375218+00:00
-- url     : https://prove2.me/submissions/791cf2e0-321b-4e88-9c78-021f8aaa6e0b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_encoding_mul_gibbs
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_pairEmbedding_mul
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_qubitY_eq
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_conj_tensorPauliX
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_conj_tensorPauliZ

section
noncomputable section
namespace QEC.Coding.BDL26PairedDecoderGibbs
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
private theorem embedding_X : pairEmbedding (dressedPauliPair S n) Qubit.pauliX = dressedX S n :=
  (dressedPauliPair S n).conj_tensorPauliX
private theorem embedding_Z : pairEmbedding (dressedPauliPair S n) Qubit.pauliZ = dressedZ S n :=
  (dressedPauliPair S n).conj_tensorPauliZ
private theorem embedding_Y : pairEmbedding (dressedPauliPair S n) Qubit.pauliY = dressedY S n := by
  rw [qubitY_eq, map_smul, pairEmbedding_mul, embedding_X, embedding_Z]
  rfl
end QEC.Coding.BDL26PairedDecoderGibbs
end
end

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
namespace QEC.Coding.BDL26PairedDecoderGibbs
theorem _root_.solution (beta : ℝ) :
    encoding S n beta Qubit.pauliY = (2 : ℂ) •
      (dressedY S n * (gibbs S (n+2) beta).toOperator) := by
  rw [encoding_mul_gibbs, embedding_Y]
end QEC.Coding.BDL26PairedDecoderGibbs
