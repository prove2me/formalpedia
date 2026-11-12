-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderGibbs.encoding_X_right
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-11T11:22:27.707833+00:00
-- url     : https://prove2.me/submissions/8abe5f9c-1ee2-4ca4-9b67-5c9cf2a9c187

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_encoding_gibbs_mul
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_conj_tensorPauliX
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

private theorem embedding_X :
    pairEmbedding (dressedPauliPair S n) Qubit.pauliX = dressedX S n := by
  have h := ThermalEncoding.PauliLikePair.conj_tensorPauliX (P := dressedPauliPair S n)
  -- h : conjOperator tensorPauliX = (dressedPauliPair S n).x
  have h1 : pairEmbedding (dressedPauliPair S n) Qubit.pauliX =
      (dressedPauliPair S n).factorization.conjOperator
        (ThermalEncoding.PauliLikePair.tensorPauliX (dressedPauliPair S n)) := rfl
  have h2 : (dressedPauliPair S n).x = dressedX S n := rfl
  exact h1.trans (h.trans h2)

theorem solution (beta : ℝ) :
    encoding S n beta Qubit.pauliX = (2 : ℂ) •
      ((gibbs S (n+2) beta).toOperator * dressedX S n) := by
  rw [encoding_gibbs_mul, embedding_X]
