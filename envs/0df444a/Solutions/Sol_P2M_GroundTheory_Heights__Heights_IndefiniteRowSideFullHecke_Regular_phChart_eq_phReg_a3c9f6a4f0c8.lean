-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_phChart_eq_phReg_a3c9f6a4f0c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:59:58.82526+00:00
-- url     : https://prove2.me/submissions/2a6d8001-684a-4f0f-9164-4122e0831db1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ProjLineChartsNotSubsetBall
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_smoothed_eq_molli_40497bc0d556

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
theorem _root_.solution [T2Space X] (R : RegChartData A) (hW : ∀ j, R.W j ⊆ ball 0 1)
    (hf : ∀ j, ContDiffOn ℝ ∞ (R.f j) (R.W j)) (ρ : Mollifier D) (K t : ℝ) (j : Fin R.n) (x : X)
    (ht : 0 < t) (hK : ∀ y ∈ ball (R.ψ j x) t, y ∉ coordDiv (R.S j) → -K ≤ R.u R.φ j y) :
    (R.toRegular hW hf).phReg ρ K t j x = R.phChart R.φ ρ t j x := by
  unfold GroundTheory.Heights₂.Heights.Regular.RegChartData.phReg
  exact congrArg (fun s => s - R.q j (R.ψ j x)) (smoothed_eq_molli (R.toRegular hW hf) ρ K t j (R.ψ j x) ht hK)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
