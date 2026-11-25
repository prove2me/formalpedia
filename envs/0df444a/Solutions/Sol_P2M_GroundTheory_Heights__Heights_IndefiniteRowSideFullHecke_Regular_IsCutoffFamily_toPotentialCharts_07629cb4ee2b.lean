-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_IsCutoffFamily_toPotentialCharts_07629cb4ee2b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:30:57.03903+00:00
-- url     : https://prove2.me/submissions/12f7ab70-9c03-430a-9993-3789562606e3

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
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
theorem _root_.solution [T2Space X] {R : RegCharts A} {hW : ∀ j, R.W j ⊆ ball 0 1}
    {C : ℝ} {η : Fin R.n → X → ℝ} (hη : R.IsCutoffFamily C η) (j : Fin R.n) :
    let P := R.toPotentialCharts hW
    A.SmoothOn (P.mid j) (η j) ∧ (∀ x ∈ P.mid j, -1 ≤ η j x ∧ η j x ≤ 0) ∧
      (∀ x ∈ P.inner j, η j x = 0) ∧
      ∃ L : Set X, IsClosed L ∧ L ⊆ P.mid j ∧ ∀ x ∈ P.mid j \ L, η j x = -1 := by
  intro P
  obtain ⟨h1, h2, h3, ⟨K, hK, hKW, hKη⟩, -⟩ := hη j
  have hKt : K ⊆ (R.ψ j).target := hKW.trans
    ((subset_closure.trans (R.closure_W'_subset j)).trans (R.W_subset j))
  refine ⟨h1, h2, h3, (R.ψ j).symm '' K,
    (hK.image_of_continuousOn ((R.ψ j).continuousOn_symm.mono hKt)).isClosed, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨(R.ψ j).map_target (hKt hy), ?_⟩
    show R.ψ j ((R.ψ j).symm y) ∈ R.W' j
    rw [(R.ψ j).right_inv (hKt hy)]
    exact hKW hy
  · rintro x ⟨hx, hxL⟩
    refine hKη x hx fun hxK => hxL ⟨R.ψ j x, hxK, ?_⟩
    exact (R.ψ j).left_inv hx.1
end IsCutoffFamily
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
