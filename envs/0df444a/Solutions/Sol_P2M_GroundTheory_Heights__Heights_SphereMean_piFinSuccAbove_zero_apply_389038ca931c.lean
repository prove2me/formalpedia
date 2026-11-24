-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_piFinSuccAbove_zero_apply_389038ca931c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:44.431679+00:00
-- url     : https://prove2.me/submissions/d1c64693-292a-48d1-9d45-480d81646083

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Measure Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean
namespace GroundTheory.Heights₂.Heights.SphereMean
theorem _root_.solution {m : ℕ} (x : Fin (m + 1) → ℂ) :
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) 0 x = (x 0, Fin.tail x) := by
  simp [MeasurableEquiv.piFinSuccAbove_apply]
end GroundTheory.Heights₂.Heights.SphereMean
