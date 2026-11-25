-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_fsLog_1e3034da99c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:22.913982+00:00
-- url     : https://prove2.me/submissions/0db51d02-5a15-4db0-bbe3-79bd25aaf1a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_dualNorm_fa5369e88d9b

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
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsHeight
theorem _root_.solution (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (u y : Fin n → ℂ) :
    fsLog (ofPointMatrix S hS) u y =
      IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS u (fun p => y p.2) := by
  simp [fsLog, IndefiniteRowSideFullHecke.ArithBezout.logFormNorm, IndefiniteRowSideFullHecke.ArithBezout.hermLine,
    ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics, ofPointMatrix_dualNorm]
end GroundTheory.Heights₂.Heights.ObjectsHeight
