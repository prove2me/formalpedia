-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderGibbs.source_even_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-11T18:03:09.700193+00:00
-- url     : https://prove2.me/submissions/a6283b8c-9010-457b-b78f-e44733c6d017

import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_readout_gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderGibbs
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale)
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_23
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_24
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_416

theorem solution (k : Nat) (hk : 1 ≤ k) (beta : ℝ) :
    ∃ n : Nat, n+2 = 2*k ∧
      channel S n (gibbs S (n+2) beta).toOperator = (2 : ℂ)⁻¹ • groundProjector S n ∧
      readout S n (gibbs S (n+2) beta).toOperator = ThermalEncoding.PauliLikePair.maximallyMixedQubit.toOperator :=
  ⟨2*(k-1), BDL26TransposedStoppedDecoder.source_even_level k hk,
    channel_gibbs S _ beta, readout_gibbs S _ beta⟩
