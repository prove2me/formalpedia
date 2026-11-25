-- Prove2me | solution 1 for PositivityTheory.ThKF.E.eq_of_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:50.78186+00:00
-- url     : https://prove2.me/submissions/9bfa0fe9-dc2e-4fb7-af2d-6dcdd8b54221

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_EqOfInner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.E
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.ThKF.E
theorem _root_.solution {u v : Sch l} (h : ∀ φ : Sch l, inner ℂ (φ.toLp 2 volume) (u.toLp 2 volume) =
    inner ℂ (φ.toLp 2 volume) (v.toLp 2 volume)) : u = v := by
  apply injective_toLp 2 volume
  have := h (u - v)
  rw [← sub_eq_zero, ← inner_sub_right, ← toLpCLM_apply (𝕜 := ℂ), map_sub] at this
  exact sub_eq_zero.1 (inner_self_eq_zero.1 this)
end PositivityTheory.ThKF.E
