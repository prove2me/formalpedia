-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_pair_b614e5fd0ac9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:25:31.263984+00:00
-- url     : https://prove2.me/submissions/ba76404e-1af2-4d73-8de5-e96967dc1fd8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncTransfer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PTruncTransfer
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_exists_lipschitz_near_3535e800fccc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_limsupExt_max_le_2c44b518e346
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_isCompact_chart_image_aa5560298c9d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_trunc_bdd_5a2b401ede64
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_mid_subset_source_96b409876f03
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RegChartData_symm_mem_Yo_ad344fcd4555
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_analyticAt_transition_63e9fc06e079
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_trunc_bdd


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
open Metric Filter Topology Set
open ReciprocityTheory.AnForm.A (coordDiv limsupExt polyMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.TruncTransfer
variable {D : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X] {A : FinHolAtlas D X}
  (R : RegChartData A)
namespace GroundTheory.Heights₂.Heights.Regular.TruncTransfer
theorem _root_.solution (j k : Fin R.N) : ∃ δ₀ > 0, ∃ c₀ > 0, ∃ L₀ B₀ : ℝ, ∀ δ L B : ℝ, δ ≤ δ₀ → L * δ ≤ c₀ →
    2 * L₀ ≤ L → 1 ≤ L → B₀ ≤ B →
    ∀ K : ℝ, ∀ x ∈ R.mid j ∩ R.mid k, ∀ t : ℝ, 0 < t → t < δ → ∀ y ∈ closedBall (R.chart j x) t,
      R.trunc K j y ≤ max (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B) +
        (R.q j (R.chart j x) - R.q k (R.chart k x)) + L * t := by
  set W := (R.chart j).target ∩ (R.chart j).symm ⁻¹' (R.chart k).source with hW
  have hWo : IsOpen W := (R.chart j).isOpen_inter_preimage_symm (R.chart k).open_source
  obtain ⟨τ, hτ⟩ : ∃ f : (Fin D → ℂ) → (Fin D → ℂ), f = R.chart k ∘ (R.chart j).symm := ⟨_, rfl⟩
  have hτy : ∀ y, τ y = R.chart k ((R.chart j).symm y) := fun y => by rw [hτ]; rfl
  obtain ⟨Δ, hΔ⟩ : ∃ f : (Fin D → ℂ) → ℝ, f = fun y => R.q j y - R.q k (τ y) := ⟨_, rfl⟩
  have hΔy : ∀ y, Δ y = R.q j y - R.q k (τ y) := fun y => by rw [hΔ]
  have hKc : IsCompact (R.chart j '' (closure (R.mid j) ∩ closure (R.mid k))) :=
    isCompact_chart_image R j inter_subset_left (isClosed_closure.inter isClosed_closure)
  have hKW : R.chart j '' (closure (R.mid j) ∩ closure (R.mid k)) ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    have hxj := R.closure_mid j hx.1
    refine ⟨(R.chart j).map_source hxj, ?_⟩
    show (R.chart j).symm (R.chart j x) ∈ (R.chart k).source
    rw [(R.chart j).left_inv hxj]
    exact R.closure_mid k hx.2
  have hτan : ∀ y ∈ W, AnalyticAt ℂ τ y := by
    intro y hy
    have h := analyticAt_transition (R.compat j) (R.compat k) ((R.chart j).map_target hy.1) hy.2
    rw [(R.chart j).right_inv hy.1] at h
    rwa [hτ]
  have hτc : ∀ y ∈ W, ContDiffAt ℝ 1 τ y := fun y hy =>
    (hτan y hy).restrictScalars.contDiffAt
  have hτT : ∀ y ∈ W, τ y ∈ (R.chart k).target := fun y hy => by
    rw [hτy]; exact (R.chart k).map_source hy.2
  have hΔc : ∀ y ∈ W, ContDiffAt ℝ 1 Δ y := by
    intro y hy
    have hqj : ContDiffAt ℝ 1 (R.q j) y :=
      ((R.q_smooth j).contDiffAt ((R.chart j).open_target.mem_nhds hy.1)).of_le (by simp)
    have hqk : ContDiffAt ℝ 1 (R.q k) (τ y) :=
      ((R.q_smooth k).contDiffAt ((R.chart k).open_target.mem_nhds (hτT y hy))).of_le (by simp)
    rw [hΔ]
    exact hqj.sub (hqk.comp y (hτc y hy))
  obtain ⟨ε₁, hε₁, C₁, hC₁, hτL⟩ := exists_lipschitz_near hWo hKc hKW hτc
  obtain ⟨ε₂, hε₂, C₂, hC₂, hΔL⟩ := exists_lipschitz_near hWo hKc hKW hΔc
  obtain ⟨B₀, hB₀⟩ := hKc.exists_bound_of_continuousOn
    (fun y hy => (hΔc y (hKW hy)).continuousAt.continuousWithinAt)
  obtain ⟨c₀, hc₀, Mk, hMk⟩ := trunc_bdd R k
  refine ⟨min ε₁ ε₂ / 2, half_pos (lt_min hε₁ hε₂), c₀, hc₀, max C₁ C₂, B₀, ?_⟩
  intro δ L B hδ hLδ hL₀ hL1 hB K x hx t ht htδ y hy
  have hxj := R.mid_subset_source j hx.1
  have hxk := R.mid_subset_source k hx.2
  have hzK : R.chart j x ∈ R.chart j '' (closure (R.mid j) ∩ closure (R.mid k)) :=
    mem_image_of_mem _ ⟨subset_closure hx.1, subset_closure hx.2⟩
  have hτz : τ (R.chart j x) = R.chart k x := by rw [hτy, (R.chart j).left_inv hxj]
  have hΔz : Δ (R.chart j x) = R.q j (R.chart j x) - R.q k (R.chart k x) := by rw [hΔy, hτz]
  have hΔB : |Δ (R.chart j x)| ≤ B₀ := by simpa [Real.norm_eq_abs] using hB₀ _ hzK
  have hLt : L * t ≤ c₀ := (mul_le_mul_of_nonneg_left htδ.le (by linarith)).trans hLδ
  have hbdd : BddAbove (R.trunc K k '' closedBall (R.chart k x) (L * t)) :=
    ⟨max Mk (-K), by rintro _ ⟨w, hw, rfl⟩; exact hMk K x hx.2 (L * t) hLt w hw⟩
  have h2t : 2 * t ≤ min ε₁ ε₂ := by linarith
  have hCL : max C₁ C₂ * (2 * t) ≤ L * t := by
    have := mul_le_mul_of_nonneg_right hL₀ ht.le
    linarith
  have hC0 : 0 ≤ max C₁ C₂ := hC₁.trans (le_max_left _ _)
  obtain ⟨hWz, hτd⟩ := hτL _ hzK
  have key : ∀ y' ∈ closedBall (R.chart j x) (2 * t), y' ∉ coordDiv (R.S j) →
      max (R.u j y') (-K) ≤ max (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B) +
        (R.q j (R.chart j x) - R.q k (R.chart k x)) + L * t := by
    intro y' hy' hy'S
    have hy'1 : y' ∈ closedBall (R.chart j x) ε₁ :=
      closedBall_subset_closedBall (h2t.trans (min_le_left _ _)) hy'
    have hy'2 : y' ∈ closedBall (R.chart j x) ε₂ :=
      closedBall_subset_closedBall (h2t.trans (min_le_right _ _)) hy'
    have hy'W : y' ∈ W := hWz hy'1
    have hnorm : ‖y' - R.chart j x‖ ≤ 2 * t := by rw [← dist_eq_norm]; exact mem_closedBall.1 hy'
    have hx'k : (R.chart j).symm y' ∈ (R.chart k).source := hy'W.2
    have hx'Yo : (R.chart j).symm y' ∈ R.Yo := R.symm_mem_Yo j hy'W.1 hy'S
    have hτS : τ y' ∉ coordDiv (R.S k) := by
      rw [hτy]; exact (R.mem_Yo k _ hx'k).1 hx'Yo
    have hu : R.u j y' = R.u k (τ y') + Δ y' := by
      simp only [RegChartData.u, PotentialCharts.chartFun]
      rw [hΔy, hτy, (R.chart k).left_inv hx'k]
      ring
    have htr : R.trunc K k (τ y') = max (R.u k (τ y')) (-K) := by
      rw [RegChartData.trunc, limsupExt, if_neg hτS]
    have hmem : τ y' ∈ closedBall (R.chart k x) (L * t) := by
      rw [mem_closedBall, dist_eq_norm, ← hτz]
      calc ‖τ y' - τ (R.chart j x)‖ ≤ C₁ * ‖y' - R.chart j x‖ := hτd y' hy'1
        _ ≤ max C₁ C₂ * (2 * t) :=
          mul_le_mul (le_max_left _ _) hnorm (norm_nonneg _) hC0
        _ ≤ L * t := hCL
    have hP : R.u k (τ y') ≤ polyMax (R.trunc K k) (R.chart k x) (L * t) :=
      calc R.u k (τ y') ≤ max (R.u k (τ y')) (-K) := le_max_left _ _
        _ = R.trunc K k (τ y') := htr.symm
        _ ≤ polyMax (R.trunc K k) (R.chart k x) (L * t) := le_csSup hbdd (mem_image_of_mem _ hmem)
    have hΔle : Δ y' ≤ Δ (R.chart j x) + L * t := by
      have h1 := (hΔL _ hzK).2 y' hy'2
      rw [Real.norm_eq_abs] at h1
      have h2 : C₂ * ‖y' - R.chart j x‖ ≤ max C₁ C₂ * (2 * t) :=
        mul_le_mul (le_max_right _ _) hnorm (norm_nonneg _) hC0
      linarith [le_abs_self (Δ y' - Δ (R.chart j x))]
    have hm1 := le_max_left (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B)
    have hm2 := le_max_right (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B)
    have hΔa := abs_le.1 hΔB
    have hLt0 : 0 ≤ L * t := mul_nonneg (by linarith) ht.le
    rw [hu]
    refine max_le ?_ ?_ <;> linarith
  have hyW : y ∈ W := hWz (closedBall_subset_closedBall
    (by linarith [min_le_left ε₁ ε₂] : t ≤ ε₁) hy)
  exact limsupExt_max_le (R.chart j).open_target _ _ K _ _ hyW.1 ht fun y' hy' _ hy'S =>
    key y' (mem_closedBall.2 (by
      linarith [dist_triangle y' y (R.chart j x), mem_ball.1 hy', mem_closedBall.1 hy])) hy'S
end GroundTheory.Heights₂.Heights.Regular.TruncTransfer
