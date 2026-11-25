-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_exists_transfer_12b2b51a69fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:47:10.219677+00:00
-- url     : https://prove2.me/submissions/177ccd04-aa64-49aa-8d4c-c492f709e18f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsCompactImageClosureMid
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartComparison
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PBoundedChartComparison
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_exists_transfer_pair_ff5ad9823de4
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_le__638c0d78514a
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_mono__555a93f5b347
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_polyMax
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
open Metric Set
open ReciprocityTheory.AnForm.A (IsPsh polyMax molli mollify_thm polyMax_le' polyMax_mono' le_polyMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.PotentialCharts
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (P : PotentialCharts A)
namespace GroundTheory.Heights₂.Heights.Regular.PotentialCharts
theorem _root_.solution [CompactSpace X] :
    ∃ δ > 0, ∃ L : ℝ, 1 ≤ L ∧ ∀ j k : Fin P.N, ∀ x ∈ P.mid j ∩ P.mid k,
      ∀ y ∈ closedBall (P.chart j x) δ,
      y ∈ (P.chart j).target ∧ (P.chart j).symm y ∈ (P.chart k).source ∧
      ‖P.chart k ((P.chart j).symm y) - P.chart k x‖ ≤ L * ‖y - P.chart j x‖ ∧
      P.q j y - P.q k (P.chart k ((P.chart j).symm y)) - (P.q j (P.chart j x) - P.q k (P.chart k x)) ≤
        L * ‖y - P.chart j x‖ := by
  choose δ hδ L hL using fun p : Fin P.N × Fin P.N => P.exists_transfer_pair p.1 p.2
  by_cases hN : Nonempty (Fin P.N × Fin P.N)
  · obtain ⟨p₀, hp₀⟩ := Finite.exists_min δ
    have hS : 0 ≤ ∑ p, |L p| := Finset.sum_nonneg fun p _ => abs_nonneg (L p)
    refine ⟨δ p₀, hδ p₀, 1 + ∑ p, |L p|, by linarith, fun j k x hx y hy => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := hL (j, k) x hx y (closedBall_subset_closedBall (hp₀ (j, k)) hy)
    have hLp : L (j, k) ≤ 1 + ∑ p, |L p| := by
      have := Finset.single_le_sum (fun p _ => abs_nonneg (L p)) (Finset.mem_univ (j, k))
      linarith [le_abs_self (L (j, k))]
    have hn := norm_nonneg (y - P.chart j x)
    exact ⟨h1, h2, h3.trans (mul_le_mul_of_nonneg_right hLp hn),
      h4.trans (mul_le_mul_of_nonneg_right hLp hn)⟩
  · exact ⟨1, one_pos, 1, le_rfl, fun j k => (hN ⟨(j, k)⟩).elim⟩
end GroundTheory.Heights₂.Heights.Regular.PotentialCharts
