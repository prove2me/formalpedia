-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RecQOfRecursion_divCycle_apply_70c37bfa12bc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:16.82638+00:00
-- url     : https://prove2.me/submissions/f6842531-be11-4ba8-948a-24e580120c82

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
open Classical
namespace GroundTheory.Heights₂.Heights.RecQOfRecursion
theorem _root_.solution (P : Ideal (MRing (PBlk n))) (s : MRing (PBlk n)) (W : Ideal (MRing (PBlk n))) :
    ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W = if W ∈ divSupp P s then multAt (P ⊔ Ideal.span {s}) W else 0 :=
  rfl
end GroundTheory.Heights₂.Heights.RecQOfRecursion
