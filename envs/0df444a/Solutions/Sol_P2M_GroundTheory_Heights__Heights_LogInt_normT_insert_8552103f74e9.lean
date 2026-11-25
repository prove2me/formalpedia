-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_normT_insert_8552103f74e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:27.634806+00:00
-- url     : https://prove2.me/submissions/1843570c-dae1-4c13-b5da-ba47f7731180

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere

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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution (h : HermNorm n) (T : Finset (Fin k)) (i : Fin k) (hi : i ∉ T)
    (u : Fin k × Fin n → ℂ) :
    normT h (insert i T) u =
      scaleP (inGroup i) ((h.norm fun j => u (i, j) : ℝ) : ℂ)⁻¹ (normT h T u) := by
  funext ij
  by_cases hij : ij.1 = i
  · have hT : ij.1 ∉ T := hij ▸ hi
    simp [normT, scaleP, inGroup, hij, hi]
  · simp [normT, scaleP, inGroup, hij]
end GroundTheory.Heights₂.Heights.LogInt
