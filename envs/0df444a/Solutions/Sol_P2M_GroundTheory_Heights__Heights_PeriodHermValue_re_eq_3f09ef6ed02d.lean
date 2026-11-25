-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PeriodHermValue_re_eq_3f09ef6ed02d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:27.417921+00:00
-- url     : https://prove2.me/submissions/b77d27a5-c489-44c6-8d3c-1ac7b09c1947

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
    (fun k => (((fun k => (α k : ℂ)) + τ *ᵥ fun k => (β k : ℂ)) k).re) =
      α + τ.map Complex.re *ᵥ β := by
  ext k
  simp [mulVec, dotProduct, Complex.re_sum, Complex.mul_re]
end GroundTheory.Heights₂.Heights.PeriodHermValue
