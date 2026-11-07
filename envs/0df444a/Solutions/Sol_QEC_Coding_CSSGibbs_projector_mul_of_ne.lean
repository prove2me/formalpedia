-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.projector_mul_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:04:23.268353+00:00
-- url     : https://prove2.me/submissions/81b886da-9ada-4f6f-8bc2-6212d509d2c8

import Definitions.Def_QEC_Coding_CSS_Syndrome
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_mul_of_ne


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
theorem _root_.solution (s t : Word (ZMod 2) (Sum κP κQ)) (hst : s ≠ t) :
    projector P Q horth s * projector P Q horth t = 0 := by
  apply jointStabilizerProjector_mul_of_ne
  exact fun h => hst ((syndromeOutcome _).injective h)
end QEC.Coding.CSSGibbs
