-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_det_of_row_zero_4634931e014b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:45.983427+00:00
-- url     : https://prove2.me/submissions/aac5ae1c-9464-4e94-97e2-e8ad68557095

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartMassInvariant

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
variable {e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
theorem _root_.solution (T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hT : ∀ j : Fin e, T 0 j.succ = 0) :
    T.det = T 0 0 * (T.submatrix Fin.succ Fin.succ).det := by
  rw [det_succ_row_zero, Fin.sum_univ_succ]
  simp [hT, Fin.succAbove_zero]
end GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
