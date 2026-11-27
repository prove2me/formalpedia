-- Prove2me | solution 1 for PositivityTheory.ThKH.Locrep.Pm_Pm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:23:41.576019+00:00
-- url     : https://prove2.me/submissions/eb684a18-0f13-4cba-b9f0-2f468b4f31b1

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_LocrepSB
import Theorems.Thm_PositivityTheory_ThKH_Locrep_Pm_apply
import Theorems.Thm_PositivityTheory_ThKH_Locrep_ev_put
import Theorems.Thm_PositivityTheory_ThKH_Locrep_put_put

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Locrep
open Filter Topology GlobalTheory.WeilM
variable {A K : Type} [AddCommGroup A] [AddCommGroup K] (ev : A →+ K) (ι : K →+ A)
variable {ev ι}
namespace PositivityTheory.ThKH.Locrep
theorem _root_.solution (h : ∀ y, ev (ι y) = y) (φ φ₁ : K → ℂ) (a y : K) (Φ : A → ℂ) :
    Pm ev ι φ a (Pm ev ι φ₁ y Φ) = φ₁ a • Pm ev ι φ y Φ := by
  funext x
  simp only [Pm_apply, ev_put h, put_put h, Pi.smul_apply, smul_eq_mul]
  ring
end PositivityTheory.ThKH.Locrep
