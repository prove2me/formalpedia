-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.selectedProjector_starProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:38:50.338763+00:00
-- url     : https://prove2.me/submissions/d779eca9-aa18-41e9-8b85-dec6c8c99e0d

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Theorems.Thm_QEC_Coding_CSSGibbs_selectedProjector_eq_badProjector
import Theorems.Thm_QEC_Coding_CSSGibbs_badProjector_adjoint
import Theorems.Thm_QEC_Coding_CSSGibbs_badProjector_square
attribute [local simp] QEC.Coding.CSSGibbs.badProjector_adjoint



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
    IsStarProjection (selectedProjector P Q horth A) := by
  rw [selectedProjector_eq_badProjector]
  refine ⟨badProjector_square P Q horth _, ?_⟩
  change LinearMap.adjoint (badProjector P Q horth _) = _
  exact badProjector_adjoint P Q horth _
end QEC.Coding.CSSGibbs
