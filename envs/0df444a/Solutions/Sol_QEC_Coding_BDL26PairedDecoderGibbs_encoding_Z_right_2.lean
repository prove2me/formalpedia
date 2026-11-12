-- Prove2me | solution 2 for QEC.Coding.BDL26PairedDecoderGibbs.encoding_Z_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:05:38.304958+00:00
-- url     : https://prove2.me/submissions/f82347f9-8902-4967-80e6-a379edf3b035

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_encoding_gibbs_mul
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
      ((gibbs S (n+2) beta).toOperator * dressedZ S n) := by
  rw [encoding_gibbs_mul, embedding_Z]
end QEC.Coding.BDL26PairedDecoderGibbs
