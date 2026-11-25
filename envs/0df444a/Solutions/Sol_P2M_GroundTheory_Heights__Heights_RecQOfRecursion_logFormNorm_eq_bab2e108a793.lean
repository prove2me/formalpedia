-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RecQOfRecursion_logFormNorm_eq_bab2e108a793
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:01.774464+00:00
-- url     : https://prove2.me/submissions/75fe1fc0-45b7-49c9-b5ac-a86e7a9c11b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MemConePointsSpanX0
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_FiniteSupportLogCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MemMinimalPrimesOfMemFundCycleSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PObjectsDivCycleGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDivSuppHorizontalArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_HeightMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRecQOfRecursion

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
noncomputable section
open GroundTheory.Heights₂.Heights.RecQOfRecursion
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt geoNum charOf arInt)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.RecQOfRecursion
theorem _root_.solution (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (u : Fin n → ℤ) :
    IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS (fun i => (u i : ℂ)) =
      ReciprocityTheory.ChartRestriction.G.Geo.logNorm (IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS) (IndefiniteRowSideFullHecke.ArithBezout.linForm u) := by
  funext z
  simp [IndefiniteRowSideFullHecke.ArithBezout.logFormNorm, ReciprocityTheory.ChartRestriction.G.Geo.logNorm, IndefiniteRowSideFullHecke.ArithBezout.linForm,
    ReciprocityTheory.ChartRestriction.G.Geo.Xc]
end GroundTheory.Heights₂.Heights.RecQOfRecursion
