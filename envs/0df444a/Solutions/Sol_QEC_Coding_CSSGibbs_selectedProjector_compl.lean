-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.selectedProjector_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:39:12.687198+00:00
-- url     : https://prove2.me/submissions/9f981758-6fd0-442d-9957-3b5b18d04b73

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Theorems.Thm_QEC_Coding_CSSGibbs_selectedProjector_total

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
theorem _root_.solution (A : Finset (Realizable P Q)) :
    selectedProjector P Q horth Aᶜ = 1 - selectedProjector P Q horth A := by
  apply eq_sub_iff_add_eq.mpr
  change (∑ a ∈ Aᶜ, projector P Q horth (realizableEmbedding P Q a)) +
    (∑ a ∈ A, projector P Q horth (realizableEmbedding P Q a)) = _
  rw [Finset.sum_compl_add_sum]
  exact selectedProjector_total P Q horth
end QEC.Coding.CSSGibbs
