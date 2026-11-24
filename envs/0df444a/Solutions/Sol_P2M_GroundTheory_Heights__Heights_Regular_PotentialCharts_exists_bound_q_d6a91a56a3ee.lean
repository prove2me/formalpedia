-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_exists_bound_q_d6a91a56a3ee
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:36.591597+00:00
-- url     : https://prove2.me/submissions/0bc81e2c-f8ef-45b8-985e-3048d539e594

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
theorem _root_.solution [CompactSpace X] {δ : ℝ}
    (hδ : ∀ j, cthickening δ ((P.chart j) '' closure (P.mid j)) ⊆ (P.chart j).target) :
    ∃ Q : ℝ, ∀ j, ∀ y ∈ cthickening δ ((P.chart j) '' closure (P.mid j)), |P.q j y| ≤ Q := by
  have h : ∀ j, ∃ Q : ℝ, ∀ y ∈ cthickening δ ((P.chart j) '' closure (P.mid j)), ‖P.q j y‖ ≤ Q :=
    fun j => (P.isCompact_image_closure_mid j).cthickening.exists_bound_of_continuousOn
      ((P.q_smooth j).continuousOn.mono (hδ j))
  choose Q hQ using h
  refine ⟨∑ j, |Q j|, fun j y hy => ?_⟩
  calc |P.q j y| = ‖P.q j y‖ := (Real.norm_eq_abs _).symm
    _ ≤ Q j := hQ j y hy
    _ ≤ |Q j| := le_abs_self _
    _ ≤ ∑ j, |Q j| := Finset.single_le_sum (fun i _ => abs_nonneg (Q i)) (Finset.mem_univ j)
end GroundTheory.Heights₂.Heights.Regular.PotentialCharts
