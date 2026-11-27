-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_isVerticalDivisorAt_line_082a519f87bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:04:30.902291+00:00
-- url     : https://prove2.me/submissions/62e89873-8f57-422e-8e24-2adec94ea009

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_LineField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_Example
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_IsVerticalDivisorAt_ofPrime_733ffd7ef5f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_isArithVar_yLine_74eda57965c2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexOrder
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
theorem _root_.solution {p : ℕ} (hp : p ≠ 0) :
    IsVerticalDivisorAt (mCoordIdeal yLine) p 0 (C (p : ℤ)) 1 :=
  IsVerticalDivisorAt.ofPrime isArithVar_yLine.2.2.1 hp
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
