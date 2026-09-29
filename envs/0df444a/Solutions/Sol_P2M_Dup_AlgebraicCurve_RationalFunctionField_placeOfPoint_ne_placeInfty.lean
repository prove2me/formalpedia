-- Prove2me | solution 1 for P2M.Dup.AlgebraicCurve.RationalFunctionField.placeOfPoint_ne_placeInfty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/70700d70-663e-51f9-bb57-bb95516a6b21

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_placeInfty_ne_ofHeightOneSpectrum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_placeOfPoint_ne_placeInfty
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

open IsDedekindDomain AlgebraicCurve AlgebraicCurve.RationalFunctionField

theorem solution (K : Type*) [Field K] [DecidableEq (RatFunc K)] (a : K) : placeOfPoint K a ≠ placeInfty K := by
  rw [placeOfPoint_eq_ofHeightOneSpectrum]
  exact fun h => AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum K _ h.symm

end S_AlgebraicCurve_RationalFunctionField_placeOfPoint_ne_placeInfty
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_placeOfPoint_ne_placeInfty (solution)
