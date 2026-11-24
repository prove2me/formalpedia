-- Prove2me | solution 1 for PositivityTheory.ThKF.E.toLp_rho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:28.025803+00:00
-- url     : https://prove2.me/submissions/aa17ca0f-ea65-48e5-9c48-035a0936bcca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_EqOfInner
import Theorems.Thm_GlobalTheory_RealWeil_coeFn_rho


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
theorem _root_.solution {w : l ⊕ l → ℝ} {f g : Sch l} (h : ⇑g = rhoFun w f) : g.toLp 2 volume = rho w (f.toLp 2 volume) := by
  refine Lp.ext ((g.coeFn_toLp 2 volume).trans ?_)
  rw [h]
  exact ((coeFn_rho w _).trans (rhoFun_congr w (f.coeFn_toLp 2 volume))).symm
end PositivityTheory.ThKF.E
