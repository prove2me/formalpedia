-- Prove2me | solution 2 for QEC.Coding.BDL26PairedDecoderGibbs.encoding_X_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:05:22.88007+00:00
-- url     : https://prove2.me/submissions/a2c6c48e-5c7d-4b0b-b6e9-8f7d8ea2ff14

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_encoding_gibbs_mul
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_conj_tensorPauliX

section
noncomputable section
namespace QEC.Coding.BDL26PairedDecoderGibbs
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
private theorem embedding_X : pairEmbedding (dressedPauliPair S n) Qubit.pauliX = dressedX S n :=
  (dressedPauliPair S n).conj_tensorPauliX
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
    encoding S n beta Qubit.pauliX = (2 : ℂ) •
      ((gibbs S (n+2) beta).toOperator * dressedX S n) := by
  rw [encoding_gibbs_mul, embedding_X]
end QEC.Coding.BDL26PairedDecoderGibbs
