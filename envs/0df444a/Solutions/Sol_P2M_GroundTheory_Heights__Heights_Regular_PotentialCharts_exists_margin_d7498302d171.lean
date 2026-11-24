-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_exists_margin_d7498302d171
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:36.834698+00:00
-- url     : https://prove2.me/submissions/ea481965-9b3b-4d0e-9850-1b37d642873b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsCompactImageClosureMid
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_isCompact_image_closure_mid_4db7e722a909

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli shrink regMax tmax)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open ReciprocityTheory.AnForm (levi)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.PotentialCharts
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (P : PotentialCharts A)
namespace GroundTheory.Heights₂.Heights.Regular.PotentialCharts
theorem _root_.solution [CompactSpace X] :
    ∃ δ > 0, ∀ j, cthickening δ ((P.chart j) '' closure (P.mid j)) ⊆ (P.chart j).target := by
  have h : ∀ j, ∃ δ, 0 < δ ∧
      cthickening δ ((P.chart j) '' closure (P.mid j)) ⊆ (P.chart j).target :=
    fun j => (P.isCompact_image_closure_mid j).exists_cthickening_subset_open
      (P.chart j).open_target
      (image_subset_iff.2 fun x hx => (P.chart j).map_source (P.closure_mid j hx))
  choose δ hδ hsub using h
  by_cases hN : Nonempty (Fin P.N)
  · obtain ⟨j₀, hj₀⟩ := Finite.exists_min δ
    exact ⟨δ j₀, hδ j₀, fun j => (cthickening_mono (hj₀ j) _).trans (hsub j)⟩
  · exact ⟨1, one_pos, fun j => (hN ⟨j⟩).elim⟩
end GroundTheory.Heights₂.Heights.Regular.PotentialCharts
