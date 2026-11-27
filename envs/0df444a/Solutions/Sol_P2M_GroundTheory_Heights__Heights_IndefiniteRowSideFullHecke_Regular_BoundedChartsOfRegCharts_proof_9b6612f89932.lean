-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_BoundedChartsOfRegCharts_proof_9b6612f89932
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:12:54.599278+00:00
-- url     : https://prove2.me/submissions/6b617b51-9742-4386-890e-924dd5a98c9e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StBoundedChartsOfRegCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ProjLineChartsNotSubsetBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PBoundedChartsOfRegCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_RegCharts_scaled_W_subset_cd3accf47d3b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open Metric Set
open ReciprocityTheory.AnForm.A (IsPsh)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
namespace BoundedChartsOfRegCharts
theorem _root_.solution : BoundedChartsOfRegCharts.Statement := by
  intro X _ _ _ D A R P
  have hb : ∀ j, ∃ M : ℝ, 0 < M ∧ closure (R.W' j) ⊆ ball 0 M := fun j =>
    (R.isCompact_closure_middle j).isBounded.subset_ball_lt 0 0
  choose M hM0 hM using hb
  exact ⟨(P.scaled M hM0 hM).toBoundedPsh (R.scaled_W_subset M hM0 hM), rfl, rfl⟩
end BoundedChartsOfRegCharts
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
