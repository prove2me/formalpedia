-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.jointProbability_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:38:22.004842+00:00
-- url     : https://prove2.me/submissions/1947510c-1511-4e16-8a62-2e89054e21e2

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Spectrum
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs
import Theorems.Thm_QEC_Coding_CSSGibbs_rowPartition_pos

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics Semantics.Davies Semantics.ThermalEncoding
open scoped BigOperators
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_28fb820634_14
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_28fb820634_15
namespace QEC.Coding.CSSGibbs
theorem _root_.solution (β : ℝ) (s : Word (ZMod 2) (Sum κP κQ)) :
    0 ≤ jointProbability P Q β s := by
  unfold jointProbability
  split_ifs
  · exact div_nonneg (Real.exp_pos _).le (mul_pos (rowPartition_pos P _) (rowPartition_pos Q _)).le
  · exact le_rfl
end QEC.Coding.CSSGibbs
