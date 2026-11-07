-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.trace_projector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:08:25.438521+00:00
-- url     : https://prove2.me/submissions/d3e91846-29a5-40ef-88be-7667b8e0acff

import Definitions.Def_QEC_Coding_CSS_Syndrome
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
import Theorems.Thm_QEC_Coding_CSSGibbs_projector_isProj

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
    LinearMap.trace ℂ (Qubit.QubitRegister ι) (projector P Q horth s) =
      (Module.finrank ℂ (sector P Q horth s) : ℂ) :=
  (projector_isProj P Q horth s).trace
end QEC.Coding.CSSGibbs
