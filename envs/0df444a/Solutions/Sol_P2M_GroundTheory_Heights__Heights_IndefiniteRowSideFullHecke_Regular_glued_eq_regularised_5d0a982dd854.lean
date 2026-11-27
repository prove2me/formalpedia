-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_glued_eq_regularised_5d0a982dd854
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:07:53.96002+00:00
-- url     : https://prove2.me/submissions/05a739f4-ad13-4acc-b178-28ea195c03ce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ProjLineChartsNotSubsetBall
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_PotentialCharts_glue_eq_pad_7acbd7ed4c16


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
    (hf : ∀ j, ContDiffOn ℝ ∞ (R.f j) (R.W j)) (ρ : Mollifier D) (K : ℝ) (η : Fin R.n → X → ℝ)
    (C t : ℝ) (x : X) (hε : 0 ≤ errorWithLinear C t)
    (hmol : ∀ j, x ∈ R.V' j → (R.toRegular hW hf).phReg ρ K t j x = R.phChart R.φ ρ t j x) :
    R.glued R.φ ρ η C t x = (R.toRegular hW hf).regularised ρ K t (errorWithLinear C t) η x := by
  obtain ⟨hc1, hc2⟩ := (R.cover x).choose_spec
  have hc : x ∈ (R.toRegular hW hf).mid (R.cover x).choose :=
    ⟨hc1, subset_closure.trans (R.closure_W''_subset _) hc2⟩
  unfold GroundTheory.Heights₂.Heights.Regular.RegChartData.regularised
  rw [PotentialCharts.glue_eq_pad _ _ hε x hc]
  unfold RegCharts.glued RegCharts.regArg
  congr 2
  funext j
  split_ifs with h1 h2 h2
  · rw [hmol j h1]
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rw [hmol _ hc]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
