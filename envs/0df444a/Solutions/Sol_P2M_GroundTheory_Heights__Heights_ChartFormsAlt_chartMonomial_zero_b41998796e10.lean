-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartFormsAlt_chartMonomial_zero_b41998796e10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:26.842642+00:00
-- url     : https://prove2.me/submissions/4f6d1868-0b62-4c4c-a405-aa95b6564fa3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ExistsFormOfMemChartRing

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartFormsAlt
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.ChartFormsAlt
theorem _root_.solution (c : (k : ι) → Fin (n k + 1)) :
    chartMonomial c (0 : ι → ℕ) = 1 := by
  simp [chartMonomial]
end GroundTheory.Heights₂.Heights.ChartFormsAlt
