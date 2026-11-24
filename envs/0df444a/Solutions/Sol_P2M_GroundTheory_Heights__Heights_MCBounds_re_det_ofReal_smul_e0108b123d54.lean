-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_re_det_ofReal_smul_e0108b123d54
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:10.707806+00:00
-- url     : https://prove2.me/submissions/c35f85b7-35ef-49eb-9410-06ecd00af8c4

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
theorem _root_.solution {k : ℕ} (s : ℝ) (H : Matrix (Fin k) (Fin k) ℂ) :
    ((s : ℂ) • H).det.re = s ^ k * H.det.re := by
  rw [det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
end MCBounds
end GroundTheory.Heights₂.Heights
