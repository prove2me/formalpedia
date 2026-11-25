-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_Y_transpose_d3179c735349
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:30.574146+00:00
-- url     : https://prove2.me/submissions/f7e9c441-d1da-4afd-a5d8-b3c99c307bdb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCBounds
open Matrix
open scoped ComplexOrder
noncomputable section
variable (D : PeriodChartData)
namespace GroundTheory.Heights₂.Heights.MCBounds
theorem _root_.solution {z : Fin D.n → ℂ} (hz : z ∈ D.U) : (D.Y z)ᵀ = D.Y z := by
  ext j k
  simp only [transpose_apply, PeriodChartData.Y, chartImag, Matrix.add_apply, map_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [show D.τ0 z k j = D.τ0 z j k from by simpa using congrFun (congrFun (D.τ0_symm z hz) j) k]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show D.B i k j = D.B i j k from by simpa using (D.B_psd i).isHermitian.apply j k]
end GroundTheory.Heights₂.Heights.MCBounds
