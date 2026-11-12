-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderGibbs.encoding_Z
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-11T11:22:27.064985+00:00
-- url     : https://prove2.me/submissions/329601ad-8403-4e32-a5d0-d77acaa104bf

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_encoding_mul_gibbs
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_conj_tensorPauliZ
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

private theorem embedding_Z :
    pairEmbedding (dressedPauliPair S n) Qubit.pauliZ = dressedZ S n := by
  have h := ThermalEncoding.PauliLikePair.conj_tensorPauliZ (P := dressedPauliPair S n)
  have h1 : pairEmbedding (dressedPauliPair S n) Qubit.pauliZ =
      (dressedPauliPair S n).factorization.conjOperator
        (ThermalEncoding.PauliLikePair.tensorPauliZ (dressedPauliPair S n)) := rfl
  have h2 : (dressedPauliPair S n).z = dressedZ S n := rfl
  exact h1.trans (h.trans h2)

theorem solution (beta : ℝ) :
    encoding S n beta Qubit.pauliZ = (2 : ℂ) •
      (dressedZ S n * (gibbs S (n+2) beta).toOperator) := by
  rw [encoding_mul_gibbs, embedding_Z]
