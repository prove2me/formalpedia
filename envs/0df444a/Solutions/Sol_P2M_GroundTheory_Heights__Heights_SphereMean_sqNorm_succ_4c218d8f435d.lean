-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_succ_4c218d8f435d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:52:48.452026+00:00
-- url     : https://prove2.me/submissions/a29a0d31-879f-4c06-abde-713b2d029533

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
    sqNorm x = ‖x 0‖ ^ 2 + sqNorm (Fin.tail x) := by
  simp [sqNorm, Fin.sum_univ_succ, Fin.tail]
end GroundTheory.Heights₂.Heights.SphereMean
