-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderGibbs.encoding_Y
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-11T11:22:26.374143+00:00
-- url     : https://prove2.me/submissions/865a422a-1c85-40c3-8751-f0f41c9eec50

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_encoding_mul_gibbs
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_conj_tensorPauliX
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_conj_tensorPauliZ
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_pairEmbedding_mul
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_qubitY_eq
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

private theorem embedding_Z :
    pairEmbedding (dressedPauliPair S n) Qubit.pauliZ = dressedZ S n := by
  have h := ThermalEncoding.PauliLikePair.conj_tensorPauliZ (P := dressedPauliPair S n)
  have h1 : pairEmbedding (dressedPauliPair S n) Qubit.pauliZ =
      (dressedPauliPair S n).factorization.conjOperator
        (ThermalEncoding.PauliLikePair.tensorPauliZ (dressedPauliPair S n)) := rfl
  have h2 : (dressedPauliPair S n).z = dressedZ S n := rfl
  exact h1.trans (h.trans h2)

private theorem embedding_Y :
    pairEmbedding (dressedPauliPair S n) Qubit.pauliY = dressedY S n := by
  rw [qubitY_eq, map_smul, pairEmbedding_mul, embedding_X, embedding_Z]
  rfl

theorem solution (beta : ℝ) :
    encoding S n beta Qubit.pauliY = (2 : ℂ) •
      (dressedY S n * (gibbs S (n+2) beta).toOperator) := by
  rw [encoding_mul_gibbs, embedding_Y]
