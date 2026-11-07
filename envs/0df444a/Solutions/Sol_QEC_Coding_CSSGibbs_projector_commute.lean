-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.projector_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:44:08.714184+00:00
-- url     : https://prove2.me/submissions/57a030fc-cec2-401b-abf6-09cebf349ccd

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Theorems.Thm_QEC_Coding_CSSGibbs_projector_mul_of_ne


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
theorem _root_.solution (s t : Word (ZMod 2) (Sum κP κQ)) :
    Commute (projector P Q horth s) (projector P Q horth t) := by
  by_cases h : s = t
  · subst t; exact Commute.refl _
  · show _ * _ = _ * _
    rw [projector_mul_of_ne P Q horth s t h,
      projector_mul_of_ne P Q horth t s (Ne.symm h)]
end QEC.Coding.CSSGibbs
