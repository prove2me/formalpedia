-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ne_of_mem_euclBall_diff_cbab76297a4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:56:11.14898+00:00
-- url     : https://prove2.me/submissions/bae34d92-16d9-4339-8cc1-51f0d5c42935

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLogDensNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_euclBall_self_2aab12e5f578


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} {x z : Fin n → ℂ} {r s : ℝ} (hr : 0 < r)
    (hz : z ∈ euclBall x s \ euclBall x r) : z ≠ x := by
  rintro rfl
  exact hz.2 (mem_euclBall_self z hr)
end GroundTheory.Heights₂.Heights
