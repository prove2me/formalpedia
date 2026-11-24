-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_linProj_zeroExt_b38aab75c095
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:38.302957+00:00
-- url     : https://prove2.me/submissions/01d4a5e0-ed85-4281-9939-6bcc83fabc9b

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
theorem _root_.solution {m k : ℕ} (π : Fin m → Fin (m + k) → ℂ) (x : EuclideanSpace ℂ (Fin m)) :
    linProj π (zeroExt m k x) = WithLp.toLp 2 ((coordPlaneBlock π).mulVec fun i => x i) := by
  ext i
  simp [linProj, zeroExt, Fin.sum_univ_add, coordPlaneBlock, Matrix.mulVec, dotProduct]
end GroundTheory.Heights₂.Heights
