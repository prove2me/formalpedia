-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_IsCutoffFamily_ofPotentialCharts_4721dcb9cfaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:33:22.989489+00:00
-- url     : https://prove2.me/submissions/646d26fd-1558-4ce8-9117-74b85e5a8eae

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_RegCharts_ofPotentialCharts_V__e06cbb41d586
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_RegCharts_ofPotentialCharts_V___3bc3db537ac2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_mid_subset_source_96b409876f03
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_abs_le_of_k__ne_3ed6a6aa9d98
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_k__integral_37214bfa7034
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_le


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
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (Mollifier molli regMax tmax kθ le_tmax tmax_le kθ_integral abs_le_of_kθ_ne)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
namespace IsCutoffFamily
theorem _root_.solution [CompactSpace X] {P : PotentialCharts A} {om : LocPot X}
    {om_pot : IsPotential A om} {om_pos : IsPosPot A om} {η : Fin P.N → X → ℝ} {Cη : ℝ}
    (hη : P.IsCutoffFamily η Cη) (j : Fin P.N) :
    let R := RegCharts.ofPotentialCharts P om om_pot om_pos
    A.SmoothOn (R.V' j) (η j) ∧ (∀ x ∈ R.V' j, -1 ≤ η j x ∧ η j x ≤ 0) ∧
      (∀ x ∈ R.V'' j, η j x = 0) ∧
      ∃ K : Set (Fin D → ℂ), IsCompact K ∧ K ⊆ R.W' j ∧ ∀ x ∈ R.V' j, R.ψ j x ∉ K → η j x = -1 := by
  intro R
  have hV' : R.V' j = P.mid j := RegCharts.ofPotentialCharts_V' P om om_pot om_pos j
  have hV'' : R.V'' j = P.inner j := RegCharts.ofPotentialCharts_V'' P om om_pot om_pos j
  rw [hV', hV'']
  obtain ⟨L, hL, hLm, hLη⟩ := hη.eq_neg_one j
  have hLs : L ⊆ (P.chart j).source := hLm.trans (P.mid_subset_source j)
  refine ⟨hη.smooth j, hη.bounds j, hη.eq_zero j, P.chart j '' L,
    hL.isCompact.image_of_continuousOn ((P.chart j).continuousOn.mono hLs), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨(P.chart j).map_source (hLs hx), ?_⟩
    show (P.chart j).symm (P.chart j x) ∈ P.mid j
    rw [(P.chart j).left_inv (hLs hx)]
    exact hLm hx
  · intro x hx hK
    exact hLη x ⟨hx, fun hxL => hK ⟨x, hxL, rfl⟩⟩
end IsCutoffFamily
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
