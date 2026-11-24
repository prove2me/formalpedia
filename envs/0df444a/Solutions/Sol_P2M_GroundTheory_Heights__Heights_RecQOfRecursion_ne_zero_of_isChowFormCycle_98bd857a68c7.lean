-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RecQOfRecursion_ne_zero_of_isChowFormCycle_98bd857a68c7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:04.948144+00:00
-- url     : https://prove2.me/submissions/5a88b76c-1709-4edc-8a0b-f604b6073039

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
theorem _root_.solution {F : Type*} [Field F] {Z : ProjCycle F n} {k : ℕ}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowFormCycle Z k f) : f ≠ 0 := by
  obtain ⟨c, hc, g, hg, rfl⟩ := hf
  exact mul_ne_zero (C_ne_zero.mpr hc)
    (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1)
end GroundTheory.Heights₂.Heights.RecQOfRecursion
