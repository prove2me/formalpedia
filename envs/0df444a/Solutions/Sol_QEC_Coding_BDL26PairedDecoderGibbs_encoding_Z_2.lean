-- Prove2me | solution 2 for QEC.Coding.BDL26PairedDecoderGibbs.encoding_Z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:04:53.899195+00:00
-- url     : https://prove2.me/submissions/714cbf6f-c5ad-4dd4-aac3-10a9dfb2e34e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_encoding_mul_gibbs
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_conj_tensorPauliZ

section
noncomputable section
namespace QEC.Coding.BDL26PairedDecoderGibbs
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
private theorem embedding_Z : pairEmbedding (dressedPauliPair S n) Qubit.pauliZ = dressedZ S n :=
  (dressedPauliPair S n).conj_tensorPauliZ
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
    encoding S n beta Qubit.pauliZ = (2 : ℂ) •
      (dressedZ S n * (gibbs S (n+2) beta).toOperator) := by
  rw [encoding_mul_gibbs, embedding_Z]
end QEC.Coding.BDL26PairedDecoderGibbs
