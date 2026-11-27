-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_regularised_eq_glued_b1e4b0abc427
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:02:09.076194+00:00
-- url     : https://prove2.me/submissions/5a332658-3ac3-4c9b-ade2-d769157628b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ProjLineChartsNotSubsetBall
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_IsCutoffFamily_toPotentialCharts_07629cb4ee2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_PotentialCharts_glue_eq_pad_7acbd7ed4c16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_RegCharts_ofPotentialCharts_V__e06cbb41d586


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
    (om_pot : IsPotential A om) (om_pos : IsPosPot A om) (ρ : Mollifier D) (K : ℝ)
    (η : Fin R.N → X → ℝ) (C t : ℝ) (x : X) (hε : 0 ≤ errorWithLinear C t)
    (hmol : ∀ j, x ∈ R.mid j →
      R.phReg ρ K t j x = (RegChartData.ofRegular R om om_pot om_pos).phChart R.ph ρ t j x) :
    R.regularised ρ K t (errorWithLinear C t) η x =
      (RegChartData.ofRegular R om om_pot om_pos).glued R.ph ρ η C t x := by
  set R' := RegChartData.ofRegular R om om_pot om_pos
  have hV : ∀ j, R'.toRegCharts.V' j = R.mid j :=
    RegCharts.ofPotentialCharts_V' R.toPotentialCharts om om_pot om_pos
  obtain ⟨hc1, hc2⟩ := (R'.cover x).choose_spec
  have hc : x ∈ R.mid (R'.cover x).choose := by
    rw [← hV]
    exact ⟨hc1, subset_closure.trans (R'.closure_W''_subset _) hc2⟩
  rw [GroundTheory.Heights₂.Heights.Regular.RegChartData.regularised, PotentialCharts.glue_eq_pad _ _ hε x hc]
  unfold RegCharts.glued RegCharts.regArg
  congr 2
  funext j
  split_ifs with h1 h2 h2
  · rw [hmol j h1]
  · exact absurd ((hV j).symm ▸ h1) h2
  · exact absurd ((hV j) ▸ h2) h1
  · rw [hmol _ hc]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
