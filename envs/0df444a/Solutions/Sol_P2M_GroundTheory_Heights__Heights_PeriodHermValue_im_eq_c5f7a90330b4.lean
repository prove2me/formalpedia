-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PeriodHermValue_im_eq_c5f7a90330b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:18.439966+00:00
-- url     : https://prove2.me/submissions/98be6085-4cb6-4bb5-8916-f05f53654b5f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPeriodHermValue

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
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.PeriodHermValue
namespace GroundTheory.Heights₂.Heights.PeriodHermValue
theorem _root_.solution {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (α β : Fin g → ℝ) :
    (fun k => (((fun k => (α k : ℂ)) + τ *ᵥ fun k => (β k : ℂ)) k).im) =
      τ.map Complex.im *ᵥ β := by
  ext k
  simp [mulVec, dotProduct, Complex.im_sum, Complex.mul_im]
end GroundTheory.Heights₂.Heights.PeriodHermValue
