-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesLineDegree_gram_line_0ccc6c520227
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:01:03.489824+00:00
-- url     : https://prove2.me/submissions/fa343034-c7c3-4da3-ba65-d26b1a799d4a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesLineDegree

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
open NumberField Matrix
open scoped nonZeroDivisors
noncomputable section
open GroundTheory.Heights₂.Heights.KLinesLineDegree
variable {K : Type} [Field K] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.KLinesLineDegree
theorem _root_.solution (d : (K →+* ℂ) → Fin n → ℝ) (σ : K →+* ℂ) (x : Fin n) :
    (gramAt (diagMetric d σ) σ (fun _ : Fin 1 => (Pi.single x 1 : Fin n → K))).det.re = d σ x := by
  rw [Matrix.det_unique]
  simp [gramAt, diagMetric, embVec, dotProduct, Matrix.mulVec_diagonal, Pi.single_apply]
end GroundTheory.Heights₂.Heights.KLinesLineDegree
