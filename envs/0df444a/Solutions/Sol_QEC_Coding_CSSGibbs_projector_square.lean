-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.projector_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:04:10.428197+00:00
-- url     : https://prove2.me/submissions/4e34a8cf-9806-4cc0-bd60-13e34e4b9f7b

import Definitions.Def_QEC_Coding_CSS_Syndrome
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics
open scoped BigOperators
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {κP κQ : Type} [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
namespace QEC.Coding.CSSGibbs
theorem _root_.solution (s : Word (ZMod 2) (Sum κP κQ)) :
    projector P Q horth s * projector P Q horth s = projector P Q horth s :=
  jointStabilizerProjector_idempotent _ _ _
end QEC.Coding.CSSGibbs
