-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_normT_univ_01f1829fb5fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:32.676873+00:00
-- url     : https://prove2.me/submissions/5287f32f-82de-4640-84c2-06e549765a64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul

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
open MeasureTheory Set MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution (h : HermNorm n) (u : Fin k × Fin n → ℂ) :
    normT h Finset.univ u = fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij := by
  funext ij
  simp [normT]
end GroundTheory.Heights₂.Heights.LogInt
