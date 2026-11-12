-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderGibbs.channel_nonzero_frequency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:20:54.004134+00:00
-- url     : https://prove2.me/submissions/bd439db0-e96c-4ae6-ad69-68bd6bef3287

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_channel_commutator
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric
import Theorems.Thm_QEC_Semantics_Davies_actualFrequency_energyDifference


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderGibbs
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_23
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_24
namespace QEC.Coding.BDL26PairedDecoderGibbs
theorem _root_.solution (A : Op S n) (omega : ℝ) (h : omega ≠ 0) :
    channel S n (Davies.actualFrequency (hamiltonian S (n+2))
      (CSSGibbs.hamiltonian_symmetric _ _) A omega) = 0 := by
  let F := Davies.actualFrequency (hamiltonian S (n+2))
    (CSSGibbs.hamiltonian_symmetric _ _) A omega
  have hf := Davies.actualFrequency_energyDifference (hamiltonian S (n+2))
    (CSSGibbs.hamiltonian_symmetric _ _) A omega
  have hc := channel_commutator S n F
  have hz : channel S n (F * hamiltonian S (n+2) - hamiltonian S (n+2) * F) = 0 := by
    rw [show F * hamiltonian S (n+2) - hamiltonian S (n+2) * F =
      -(hamiltonian S (n+2) * F - F * hamiltonian S (n+2)) by abel, map_neg, hc, neg_zero]
  change channel S n (Davies.energyDifference (hamiltonian S (n+2)) F) = 0 at hz
  rw [hf, map_smul] at hz
  exact (smul_eq_zero.mp hz).resolve_left (Complex.ofReal_ne_zero.mpr h)
end QEC.Coding.BDL26PairedDecoderGibbs
