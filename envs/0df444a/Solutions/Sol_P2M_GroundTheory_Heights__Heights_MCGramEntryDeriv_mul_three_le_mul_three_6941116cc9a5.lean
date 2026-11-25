-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCGramEntryDeriv_mul_three_le_mul_three_6941116cc9a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:15.879819+00:00
-- url     : https://prove2.me/submissions/671289cf-f0a6-4029-8558-7e72fba3d160

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PGramEntryDeriv

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
open GroundTheory.Heights₂.Heights.MCGramEntryDeriv
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GroundTheory.Heights₂.Heights.MCGramEntryDeriv
theorem _root_.solution {x y z X Y W : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z) (hx : x ≤ X)
    (hy : y ≤ Y) (hz : z ≤ W) : x * y * z ≤ X * Y * W :=
  mul_le_mul (mul_le_mul hx hy hy0 (hx0.trans hx)) hz hz0
    (mul_nonneg (hx0.trans hx) (hy0.trans hy))
end GroundTheory.Heights₂.Heights.MCGramEntryDeriv
