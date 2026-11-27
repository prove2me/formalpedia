-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_BoundedChartComparison_proof_38c3cfbe5458
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:08:29.621947+00:00
-- url     : https://prove2.me/submissions/5ca98a1d-2866-43d9-b64c-a159854c6b61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsCompactImageClosureMid
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartComparison
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PBoundedChartComparison
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_exists_transfer_12b2b51a69fb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_exists_bound_q_d6a91a56a3ee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_exists_margin_d7498302d171
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_log_inv_facts_1450b9e21f5d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_mollifier_exists_bound_8f667b4839a6
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
namespace GroundTheory.Heights₂.Heights.Regular
namespace BoundedChartComparison
theorem _root_.solution (h0 : MollifiedLowerBound.Statement)
    (h1 : PolyMaxOscillation.Statement) : BoundedChartComparison.Statement := by
  intro X _ _ _ D A B ρ
  obtain ⟨δ, hδ, hmarg⟩ := B.exists_margin
  obtain ⟨Q, hQ⟩ := B.exists_bound_q hmarg
  obtain ⟨Cφ, hCφ⟩ := B.bdd
  obtain ⟨δ₁, hδ₁, L, hL, hT⟩ := B.exists_transfer
  obtain ⟨b, hb⟩ := mollifier_exists_bound ρ
  have hb0 : 0 ≤ b := (ρ.nonneg 0).trans (hb 0)
  obtain ⟨c₀, hc₀⟩ : ∃ c : ℝ, c = Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; positivity
  obtain ⟨B₀, hB₀⟩ : ∃ c : ℝ, c = |Q| + |Cφ| := ⟨_, rfl⟩
  have hB₀0 : 0 ≤ B₀ := by rw [hB₀]; positivity

  have hball : ∀ k : Fin B.N, ∀ x ∈ B.mid k, ∀ r, r ≤ δ →
      closedBall (B.chart k x) r ⊆ (B.chart k).target := fun k x hx r hr =>
    (closedBall_subset_closedBall hr).trans
      ((closedBall_subset_cthickening (mem_image_of_mem _ (subset_closure hx)) δ).trans (hmarg k))
  have hbd : ∀ k : Fin B.N, ∀ x ∈ B.mid k, ∀ y ∈ closedBall (B.chart k x) δ, |B.u k y| ≤ B₀ := by
    intro k x hx y hy
    have e1 := hQ k y (closedBall_subset_cthickening (mem_image_of_mem _ (subset_closure hx)) δ hy)
    have e2 := hCφ ((B.chart k).symm y)
    have e3 : |B.u k y| ≤ |B.q k y| + |B.ph ((B.chart k).symm y)| := abs_add_le _ _
    rw [hB₀]
    linarith [le_abs_self Q, le_abs_self Cφ]
  have hpsh : ∀ k : Fin B.N, IsPsh (B.chart k).target (B.u k) := fun k => B.u_psh k
  obtain ⟨C₁, hC₁⟩ : ∃ c : ℝ, c = L + 2 := ⟨_, rfl⟩
  have hC₁3 : 3 ≤ C₁ := by linarith
  obtain ⟨a, ha⟩ : ∃ c : ℝ, c = |Real.log (δ / C₁)| := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := ha ▸ abs_nonneg _
  have hlog4 : 0 ≤ Real.log (4 * C₁ ^ 2) := Real.log_nonneg (by nlinarith)
  obtain ⟨E, hE⟩ : ∃ c : ℝ, c = (1 + c₀) * (4 * Real.log (4 * C₁ ^ 2) * B₀) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ c : ℝ, c = max E L := ⟨_, rfl⟩
  have hCE : E ≤ C := hC ▸ le_max_left _ _
  have hCL : L ≤ C := hC ▸ le_max_right _ _
  have hC₁2 : 0 < C₁ + 2 := by linarith
  refine ⟨C, min δ₁ (min (δ / (C₁ + 2)) (Real.exp (-(Real.exp 1 + 2 * a)))),
    lt_min hδ₁ (lt_min (div_pos hδ hC₁2) (Real.exp_pos _)), ?_⟩
  intro t ht ht₀
  simp only [lt_min_iff] at ht₀
  obtain ⟨htδ₁, htδ, hte⟩ := ht₀
  have hCt : t * (C₁ + 2) < δ := (lt_div_iff₀ hC₁2).1 htδ
  have hCt' : t * (C₁ + 2) = C₁ * t + 2 * t := by ring
  have hC₁t : C₁ * t ≤ δ := by linarith
  have hC₁tlt : C₁ * t < δ := by linarith
  have htLt : t ≤ L * t := le_mul_of_one_le_left ht.le hL
  have hLt : L * t ≤ C₁ * t := mul_le_mul_of_nonneg_right (by linarith) ht.le
  have h2t : 2 * t ≤ C₁ * t := mul_le_mul_of_nonneg_right (by linarith) ht.le
  obtain ⟨hℓa, -⟩ := log_inv_facts ht ha0 hte
  have hℓ0 : 0 < Real.log t⁻¹ := by linarith [Real.exp_pos 1]
  have hden : Real.log t⁻¹ / 2 ≤ Real.log (δ / (C₁ * t)) := by
    rw [show δ / (C₁ * t) = (δ / C₁) * t⁻¹ by field_simp,
      Real.log_mul (div_pos hδ (by linarith)).ne' (inv_pos.2 ht).ne']
    have := neg_abs_le (Real.log (δ / C₁))
    rw [← ha] at this
    linarith [Real.exp_pos 1]
  have hden0 : 0 < Real.log (δ / (C₁ * t)) := by linarith
  have key : ∀ j k : Fin B.N, ∀ x ∈ B.mid j ∩ B.mid k,
      B.phReg ρ t j x - B.phReg ρ t k x ≤ E / Real.log t⁻¹ + L * t := by
    intro j k x hx
    have hpj := hpsh j
    have hpk := hpsh k

    have hi : molli ρ t (B.u j) (B.chart j x) ≤ polyMax (B.u j) (B.chart j x) t :=
      (((mollify_thm D ρ _ (B.u j) (B.chart j).open_target hpj).1 t ht).2.2.2 (B.chart j x)
        (hball j x hx.1 t (by linarith))).2

    have hii : polyMax (B.u j) (B.chart j x) t ≤ polyMax (B.u k) (B.chart k x) (L * t) +
        (B.q j (B.chart j x) - B.q k (B.chart k x)) + L * t := by
      refine polyMax_le' ht.le fun y hy => ?_
      obtain ⟨-, hyk, hτ, hg⟩ := hT j k x hx y (closedBall_subset_closedBall htδ₁.le hy)
      have hyt : ‖y - B.chart j x‖ ≤ t := by rw [← dist_eq_norm]; exact hy
      have hLy := mul_le_mul_of_nonneg_left hyt (by linarith : (0 : ℝ) ≤ L)
      have hτ' : B.chart k ((B.chart j).symm y) ∈ closedBall (B.chart k x) (L * t) := by
        rw [mem_closedBall, dist_eq_norm]
        exact hτ.trans hLy
      have hle := le_polyMax hpk.1 (hball k x hx.2 (L * t) (by linarith)) hτ'
      have hu : B.u j y = B.u k (B.chart k ((B.chart j).symm y)) +
          (B.q j y - B.q k (B.chart k ((B.chart j).symm y))) := by
        simp only [BoundedPshData.u, PotentialCharts.chartFun, (B.chart k).left_inv hyk]
        ring
      linarith
    have mono : ∀ s s', 0 ≤ s → s ≤ s' → s' ≤ δ →
        polyMax (B.u k) (B.chart k x) s ≤ polyMax (B.u k) (B.chart k x) s' :=
      fun s s' hs hss' hs' => polyMax_mono' hpk.1 hs hss' (hball k x hx.2 _ hs')
    have e1 := mono (L * t) (C₁ * t) (by linarith) hLt hC₁t
    have h4C : 0 < 4 * C₁ := by linarith
    have hq : t / (4 * C₁) ≤ t / 4 := div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith)
    have e2 := mono (t / (4 * C₁)) (t / 4) (by positivity) hq (by linarith)
    have e3 := mono (t / 4) (2 * t) (by positivity) (by linarith) (by linarith)
    have e4 := mono (2 * t) (C₁ * t) (by positivity) h2t hC₁t

    have hiv := h0 D ρ b _ (B.u k) (B.chart k x) t (B.chart k).open_target hpk ht
      (hball k x hx.2 _ (by linarith)) hb
    rw [← hc₀] at hiv

    have hv := h1 D _ (B.u k) (B.chart k x) δ t C₁ (B.chart k).open_target hpk
      (hball k x hx.2 δ le_rfl) ht (by linarith) hC₁tlt
    have hMδ : polyMax (B.u k) (B.chart k x) δ ≤ B₀ :=
      polyMax_le' hδ.le fun y hy => (le_abs_self _).trans (hbd k x hx.2 y hy)
    have hMC : -B₀ ≤ polyMax (B.u k) (B.chart k x) (C₁ * t) :=
      (neg_le_of_abs_le (hbd k x hx.2 _ (mem_closedBall_self hδ.le))).trans
        (le_polyMax hpk.1 (hball k x hx.2 _ hC₁t) (mem_closedBall_self (by positivity)))
    have hN : polyMax (B.u k) (B.chart k x) δ - polyMax (B.u k) (B.chart k x) (C₁ * t) ≤ 2 * B₀ := by
      linarith
    have hO : polyMax (B.u k) (B.chart k x) (C₁ * t) - polyMax (B.u k) (B.chart k x) (t / (4 * C₁)) ≤
        4 * Real.log (4 * C₁ ^ 2) * B₀ / Real.log t⁻¹ := by
      refine hv.trans ?_
      rw [div_le_div_iff₀ hden0 hℓ0]
      calc Real.log (4 * C₁ ^ 2) * (polyMax (B.u k) (B.chart k x) δ -
              polyMax (B.u k) (B.chart k x) (C₁ * t)) * Real.log t⁻¹
          ≤ Real.log (4 * C₁ ^ 2) * (2 * B₀) * Real.log t⁻¹ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN hlog4) hℓ0.le
        _ = 4 * Real.log (4 * C₁ ^ 2) * B₀ * (Real.log t⁻¹ / 2) := by ring
        _ ≤ 4 * Real.log (4 * C₁ ^ 2) * B₀ * Real.log (δ / (C₁ * t)) :=
            mul_le_mul_of_nonneg_left hden (mul_nonneg (mul_nonneg (by norm_num) hlog4) hB₀0)
    have hc : c₀ * (polyMax (B.u k) (B.chart k x) (2 * t) - polyMax (B.u k) (B.chart k x) (t / 4)) ≤
        c₀ * (polyMax (B.u k) (B.chart k x) (C₁ * t) -
          polyMax (B.u k) (B.chart k x) (t / (4 * C₁))) :=
      mul_le_mul_of_nonneg_left (by linarith) hc₀0
    have hfin : (1 + c₀) * (polyMax (B.u k) (B.chart k x) (C₁ * t) -
          polyMax (B.u k) (B.chart k x) (t / (4 * C₁))) ≤ E / Real.log t⁻¹ := by
      rw [hE, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hO (by linarith)
    have hsum : polyMax (B.u k) (B.chart k x) (L * t) - polyMax (B.u k) (B.chart k x) (2 * t) +
          c₀ * (polyMax (B.u k) (B.chart k x) (2 * t) - polyMax (B.u k) (B.chart k x) (t / 4)) ≤
        (1 + c₀) * (polyMax (B.u k) (B.chart k x) (C₁ * t) -
          polyMax (B.u k) (B.chart k x) (t / (4 * C₁))) := by
      have h' : polyMax (B.u k) (B.chart k x) (L * t) - polyMax (B.u k) (B.chart k x) (2 * t) ≤
          polyMax (B.u k) (B.chart k x) (C₁ * t) - polyMax (B.u k) (B.chart k x) (t / (4 * C₁)) := by
        linarith
      linarith
    simp only [BoundedPshData.phReg, BoundedPshData.smoothed]
    linarith
  intro j k x hx
  have hEC : E / Real.log t⁻¹ + L * t ≤ C / Real.log t⁻¹ + C * t :=
    add_le_add (div_le_div_of_nonneg_right hCE hℓ0.le) (mul_le_mul_of_nonneg_right hCL ht.le)
  exact abs_sub_le_iff.2 ⟨(key j k x hx).trans hEC, (key k j x ⟨hx.2, hx.1⟩).trans hEC⟩
end BoundedChartComparison
end GroundTheory.Heights₂.Heights.Regular
