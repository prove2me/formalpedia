-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.rowProbability_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:39:58.097106+00:00
-- url     : https://prove2.me/submissions/f5ae5a11-caab-4328-932b-31370852062a

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Theorems.Thm_QEC_Coding_CSSGibbs_sum_rowProbability


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
theorem _root_.solution (t : ℝ) (A : Finset (LinearMap.range P)) :
    (∑ u ∈ Aᶜ, rowProbability P t u) = 1 - ∑ u ∈ A, rowProbability P t u := by
  apply eq_sub_iff_add_eq.mpr
  rw [Finset.sum_compl_add_sum, sum_rowProbability]
end QEC.Coding.CSSGibbs
