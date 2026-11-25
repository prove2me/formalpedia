-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_map_smul_one_sub_741c37bc6f53
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:38.438158+00:00
-- url     : https://prove2.me/submissions/58ce9208-b880-4ac1-8535-ee41cc1d56c4

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
theorem _root_.solution {g : ℕ} (s : ℝ) (A : Matrix (Fin g) (Fin g) ℝ) :
    (s • (1 : Matrix (Fin g) (Fin g) ℝ) - A).map (fun x : ℝ => (x : ℂ)) =
      (s : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ) - A.map (fun x : ℝ => (x : ℂ)) := by
  ext j k
  by_cases h : j = k <;> simp [h]
end MCBounds
end GroundTheory.Heights₂.Heights
