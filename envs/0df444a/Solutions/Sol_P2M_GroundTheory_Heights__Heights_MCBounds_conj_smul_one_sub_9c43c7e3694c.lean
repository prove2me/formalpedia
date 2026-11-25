-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_conj_smul_one_sub_9c43c7e3694c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:31.195802+00:00
-- url     : https://prove2.me/submissions/0182ee41-d245-48d8-bb49-d4ec5e166845

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartBounds

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
open Matrix MCBounds
open scoped ComplexOrder
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace MCBounds
theorem _root_.solution {g k : ℕ} (F : Matrix (Fin g) (Fin k) ℂ) (s : ℂ)
    (Z : Matrix (Fin g) (Fin g) ℂ) :
    Fᴴ * (s • (1 : Matrix (Fin g) (Fin g) ℂ) - Z) * F = s • (Fᴴ * F) - Fᴴ * Z * F := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
end MCBounds
end GroundTheory.Heights₂.Heights
