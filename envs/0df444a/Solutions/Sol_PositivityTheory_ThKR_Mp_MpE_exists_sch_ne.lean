-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.MpE.exists_sch_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:32:47.313712+00:00
-- url     : https://prove2.me/submissions/6988cf40-1aae-4882-bf79-e9b193b1f263

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticGroupT2Space
import Theorems.Thm_GlobalTheory_RealWeil_schwartzToL2_apply
import Theorems.Thm_PositivityTheory_ThKF_E_exists_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real ContDiff
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open PositivityTheory.ThKR.Mp.MpE
namespace PositivityTheory.ThKR.Mp.MpE
theorem _root_.solution : ∃ f : Sch l, schwartzToL2 l f ≠ 0 := by
  obtain ⟨φ, hφ⟩ := exists_ne_zero (l := l) 0
  refine ⟨φ, fun h => hφ ?_⟩
  have : φ = 0 := injective_toLp 2 volume
    (show φ.toLp 2 volume = (0 : Sch l).toLp 2 volume by
      rw [← schwartzToL2_apply, ← schwartzToL2_apply, h, map_zero])
  simp [this]
end PositivityTheory.ThKR.Mp.MpE
