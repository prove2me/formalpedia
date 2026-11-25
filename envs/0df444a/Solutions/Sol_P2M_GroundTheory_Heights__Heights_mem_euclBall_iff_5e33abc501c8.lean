-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_euclBall_iff_5e33abc501c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:39:20.625796+00:00
-- url     : https://prove2.me/submissions/3f6f9695-e5e5-4632-a4e6-703b7b5890f7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongMono

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
theorem _root_.solution {n : ℕ} (x y : Fin n → ℂ) (ρ : ℝ) :
    y ∈ euclBall x ρ ↔ dist (WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 x) < ρ := by
  rw [EuclideanSpace.dist_eq]
  simp [euclBall, euclPot, dist_eq_norm]
end GroundTheory.Heights₂.Heights
