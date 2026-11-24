-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.iso_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:01.333134+00:00
-- url     : https://prove2.me/submissions/65d0e477-eeb1-4ac8-a84a-fe6719738760

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Theorems.Thm_GlobalTheory_RealWeil_schwartzToL2_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]
namespace PositivityTheory.ThKR.LL
theorem _root_.solution {S : Sch l →L[ℂ] Sch l} (h : ∀ f : Sch l, ∫ x, ‖S f x‖ ^ (2 : ℝ) = ∫ x, ‖f x‖ ^ (2 : ℝ)) : Iso S :=
  fun f => by
    rw [schwartzToL2_apply, schwartzToL2_apply, norm_toLp' (by simp) (by simp), norm_toLp' (by simp) (by simp)]
    simp only [ENNReal.toReal_ofNat, h]
end PositivityTheory.ThKR.LL
