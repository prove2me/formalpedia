-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_RegCharts_scaled_W_subset_cd3accf47d3b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:17:12.674795+00:00
-- url     : https://prove2.me/submissions/f3a1ba39-cf7c-455d-967a-4e7019ac553c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StBoundedChartsOfRegCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ProjLineChartsNotSubsetBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PBoundedChartsOfRegCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_scaleHom_preimage_ball_ef6f63a16784

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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.RegCharts
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
variable (R : RegCharts A) (M : Fin R.n → ℝ) (hM0 : ∀ j, 0 < M j)
  (hM : ∀ j, closure (R.W' j) ⊆ ball 0 (M j))
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.RegCharts
theorem _root_.solution (j : Fin R.n) : (R.scaled M hM0 hM).W j ⊆ ball 0 1 :=
  (preimage_mono inter_subset_right).trans (scaleHom_preimage_ball D (hM0 j))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.RegCharts
