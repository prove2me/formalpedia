-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_phReg_eq_phChart_8dbb7f2f94ca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:06:04.202988+00:00
-- url     : https://prove2.me/submissions/5043b399-4d74-43ae-9de8-cb1e114d1790

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
theorem _root_.solution [CompactSpace X] (R : RegChartDataA A) (om : LocPot X)
    (om_pot : IsPotential A om) (om_pos : IsPosPot A om) (ρ : Mollifier D) (K t : ℝ) (j : Fin R.N)
    (x : X) (ht : 0 < t)
    (hK : ∀ y ∈ ball (R.chart j x) t, y ∉ coordDiv (R.S j) → -K ≤ R.u j y) :
    R.phReg ρ K t j x = (RegChartData.ofRegular R om om_pot om_pos).phChart R.ph ρ t j x := by
  unfold GroundTheory.Heights₂.Heights.Regular.RegChartData.phReg
  rw [smoothed_eq_molli R ρ K t j _ ht hK]
  rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
