-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_exists_transfer_pair_ff5ad9823de4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:39:38.771821+00:00
-- url     : https://prove2.me/submissions/ce7fe3ad-c033-474a-9632-4d631e7ade21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsCompactImageClosureMid
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartComparison
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PBoundedChartComparison
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_exists_lipschitz_near_compact_eeaef94d801a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_mid_subset_source_96b409876f03
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_analyticAt_transition_63e9fc06e079
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_le__638c0d78514a
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_mono__555a93f5b347
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMean_isOpen_inter_preimage
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
theorem _root_.solution [CompactSpace X] (j k : Fin P.N) :
    ∃ δ > 0, ∃ L : ℝ, ∀ x ∈ P.mid j ∩ P.mid k, ∀ y ∈ closedBall (P.chart j x) δ,
      y ∈ (P.chart j).target ∧ (P.chart j).symm y ∈ (P.chart k).source ∧
      ‖P.chart k ((P.chart j).symm y) - P.chart k x‖ ≤ L * ‖y - P.chart j x‖ ∧
      P.q j y - P.q k (P.chart k ((P.chart j).symm y)) - (P.q j (P.chart j x) - P.q k (P.chart k x)) ≤
        L * ‖y - P.chart j x‖ := by
  set K := (P.chart j) '' (closure (P.mid j) ∩ closure (P.mid k)) with hKdef
  set W := (P.chart j).target ∩ (P.chart j).symm ⁻¹' (P.chart k).source with hWdef
  have hK : IsCompact K := (isClosed_closure.inter isClosed_closure).isCompact.image_of_continuousOn
    ((P.chart j).continuousOn.mono (inter_subset_left.trans (P.closure_mid j)))
  have hW : IsOpen W := (P.chart j).continuousOn_symm.isOpen_inter_preimage (P.chart j).open_target
    (P.chart k).open_source
  have hKW : K ⊆ W := by
    rintro _ ⟨x, ⟨hxj, hxk⟩, rfl⟩
    exact ⟨(P.chart j).map_source (P.closure_mid j hxj), by
      simp [(P.chart j).left_inv (P.closure_mid j hxj), P.closure_mid k hxk]⟩
  have hτ : ∀ y ∈ W, ContDiffAt ℝ 1 (P.chart k ∘ (P.chart j).symm) y := by
    intro y hy
    have h := analyticAt_transition (P.compat j) (P.compat k) ((P.chart j).map_target hy.1) hy.2
    rw [(P.chart j).right_inv hy.1] at h
    exact (h.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hg : ∀ y ∈ W, ContDiffAt ℝ 1
      (fun y => P.q j y - P.q k ((P.chart k ∘ (P.chart j).symm) y)) y := by
    intro y hy
    have h1 : ContDiffAt ℝ 1 (P.q j) y :=
      ((P.q_smooth j).contDiffAt ((P.chart j).open_target.mem_nhds hy.1)).of_le (by simp)
    have h2 : ContDiffAt ℝ 1 (P.q k) ((P.chart k ∘ (P.chart j).symm) y) :=
      ((P.q_smooth k).contDiffAt
        ((P.chart k).open_target.mem_nhds ((P.chart k).map_source hy.2))).of_le (by simp)
    exact h1.sub (h2.comp y (hτ y hy))
  obtain ⟨δ₁, hδ₁, L₁, h₁⟩ := exists_lipschitz_near_compact hK hW hKW hτ
  obtain ⟨δ₂, hδ₂, L₂, h₂⟩ := exists_lipschitz_near_compact hK hW hKW hg
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, max L₁ L₂, fun x hx y hy => ?_⟩
  have hxK : P.chart j x ∈ K := mem_image_of_mem _ ⟨subset_closure hx.1, subset_closure hx.2⟩
  obtain ⟨hyW, e₁⟩ := h₁ _ hxK y (closedBall_subset_closedBall (min_le_left _ _) hy)
  obtain ⟨-, e₂⟩ := h₂ _ hxK y (closedBall_subset_closedBall (min_le_right _ _) hy)
  have hxj : (P.chart j).symm (P.chart j x) = x := (P.chart j).left_inv (P.mid_subset_source j hx.1)
  simp only [Function.comp_apply, hxj] at e₁ e₂
  have hn : 0 ≤ ‖y - P.chart j x‖ := norm_nonneg _
  refine ⟨hyW.1, hyW.2, e₁.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hn), ?_⟩
  rw [Real.norm_eq_abs] at e₂
  exact (le_abs_self _).trans (e₂.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hn))
end GroundTheory.Heights₂.Heights.Regular.PotentialCharts
