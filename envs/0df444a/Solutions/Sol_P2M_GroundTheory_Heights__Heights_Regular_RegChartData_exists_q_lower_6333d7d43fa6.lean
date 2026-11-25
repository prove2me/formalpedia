-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_RegChartData_exists_q_lower_6333d7d43fa6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:32:25.422142+00:00
-- url     : https://prove2.me/submissions/f23afa44-0292-4772-ac66-10c7a61d3a0c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartComparison
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PMollifiedNearSmooth
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_le__638c0d78514a
import Theorems.Thm_ReciprocityTheory_AnForm_A_mollify_thm


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
open Metric
open scoped ContDiff
open ReciprocityTheory.AnForm.A (polyMax molli mollify_thm polyMax_le' coordDiv limsupExt)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.RegChartData
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}
  (R : RegChartData A)
namespace GroundTheory.Heights₂.Heights.Regular.RegChartData
theorem _root_.solution [CompactSpace X] :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ j, ∀ x ∈ R.mid j, -Q ≤ R.q j (R.chart j x) := by
  have h : ∀ j, ∃ m : ℝ, ∀ x ∈ R.mid j, m ≤ R.q j (R.chart j x) := by
    intro j
    have hK : IsCompact (R.chart j '' closure (R.mid j)) :=
      isClosed_closure.isCompact.image_of_continuousOn
        ((R.chart j).continuousOn.mono (R.closure_mid j))
    have hsub : R.chart j '' closure (R.mid j) ⊆ (R.chart j).target := by
      rintro _ ⟨x, hx, rfl⟩
      exact (R.chart j).map_source (R.closure_mid j hx)
    obtain ⟨m, hm⟩ := hK.bddBelow_image ((R.q_smooth j).continuousOn.mono hsub)
    exact ⟨m, fun x hx => hm ⟨R.chart j x, ⟨x, subset_closure hx, rfl⟩, rfl⟩⟩
  choose m hm using h
  refine ⟨∑ j, |m j|, Finset.sum_nonneg fun j _ => abs_nonneg _, fun j x hx => ?_⟩
  have h1 : |m j| ≤ ∑ j, |m j| :=
    Finset.single_le_sum (f := fun j => |m j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
  have h2 := hm j x hx
  linarith [neg_abs_le (m j)]
end GroundTheory.Heights₂.Heights.Regular.RegChartData
