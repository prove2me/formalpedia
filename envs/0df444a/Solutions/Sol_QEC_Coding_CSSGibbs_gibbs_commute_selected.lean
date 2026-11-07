-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.gibbs_commute_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:39:17.792247+00:00
-- url     : https://prove2.me/submissions/3577bff7-0337-45a2-bab6-8a59338bedae

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Theorems.Thm_QEC_Coding_CSSGibbs_projector_commute_selected
import Theorems.Thm_QEC_Coding_CSSGibbs_gibbs_normalized_exp
import Theorems.Thm_QEC_Coding_CSSGibbs_thermalExponential_resolution


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical Semantics
open scoped BigOperators
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_807a85e857_19
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_807a85e857_20
namespace QEC.Coding.CSSGibbs
theorem _root_.solution (β : ℝ) (A : Finset (Realizable P Q)) :
    Commute (gibbs P Q β).toOperator (selectedProjector P Q horth A) := by
  rw [gibbs_normalized_exp, thermalExponential_resolution P Q horth]
  apply Commute.smul_left
  apply Commute.sum_left
  intro s _
  exact (projector_commute_selected P Q horth s A).smul_left _
end QEC.Coding.CSSGibbs
