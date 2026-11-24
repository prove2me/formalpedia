-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_eval_coordPlaneDetPoly_d84d2f98ec4d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:57.410422+00:00
-- url     : https://prove2.me/submissions/33cb85c6-a44c-4eae-b25d-e40be0ac56ca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre

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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m k : ℕ} (u : Fin m × Fin (m + k) → ℂ) :
    eval u (coordPlaneDetPoly m k) = (coordPlaneBlock (Function.curry u)).det := by
  rw [coordPlaneDetPoly, RingHom.map_det]
  congr 1
  ext i j
  simp [coordPlaneBlock, RingHom.mapMatrix_apply, Function.curry]
end GroundTheory.Heights₂.Heights
