-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.projector_commute_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:46:52.632185+00:00
-- url     : https://prove2.me/submissions/d46f9933-7bec-4c82-9588-a55b268684c5

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Theorems.Thm_QEC_Coding_CSSGibbs_projector_commute

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
theorem _root_.solution (s : Word (ZMod 2) (Sum κP κQ))
    (A : Finset (Realizable P Q)) :
    Commute (projector P Q horth s) (selectedProjector P Q horth A) := by
  unfold selectedProjector
  apply Commute.sum_right
  intro a _
  exact projector_commute P Q horth s _
end QEC.Coding.CSSGibbs
