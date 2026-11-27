-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_BoundedThPsh_toBoundedPsh_ph_f045e4f4b7be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:59:58.551083+00:00
-- url     : https://prove2.me/submissions/23fd5a0e-3e80-4e37-83f0-5f36b8d5dfdc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ProjLineChartsNotSubsetBall

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
open MeasureTheory Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli regMax coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts BoundedPshData pointReg pointCharts pointAtlas)
local notation "RegChartDataA" => GroundTheory.Heights₂.Heights.Regular.RegChartData
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.BoundedThPsh
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.BoundedThPsh
theorem _root_.solution [T2Space X] {R : RegCharts A} (P : BoundedThPsh R)
    (hW : ∀ j, R.W j ⊆ ball 0 1) : (P.toBoundedPsh hW).ph = P.φ := rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.BoundedThPsh
