-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_ChartComparison_proof_cb37c5d74969
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:32:39.692831+00:00
-- url     : https://prove2.me/submissions/a3abb4be-960b-4200-80fb-953d7a8f6ab9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncTransfer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartComparison
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_log_inv_facts_1450b9e21f5d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_mollifier_exists_bound_8f667b4839a6
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_le__638c0d78514a
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_mono__555a93f5b347
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
open ReciprocityTheory.AnForm.A (polyMax molli mollify_thm polyMax_le' polyMax_mono')
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
namespace ChartComparison
theorem _root_.solution (h0 : MollifiedLowerBound.Statement)
    (h1 : PolyMaxOscillation.Statement) (h2 : PolyMaxLowerBound.Statement)
    (h3 : TruncPsh.Statement) (h4 : TruncTransfer.Statement) : ChartComparison.Statement := by
  intro X _ _ _ D A R ρ
  obtain ⟨δ, B₀, hδ, hV⟩ := h3 X D A R
  choose V hVo _hVt hVball hVpsh using hV
  obtain ⟨δ₁, L, B₁, hδ₁, hL, hT⟩ := h4 X D A R
  obtain ⟨C₂, t₂, ht₂, hlow⟩ := h2 X D A R
  obtain ⟨b, hb⟩ := mollifier_exists_bound ρ
  have hb0 : 0 ≤ b := (ρ.nonneg 0).trans (hb 0)
  obtain ⟨c₀, hc₀⟩ : ∃ c : ℝ, c = Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; positivity
  obtain ⟨C₁, hC₁⟩ : ∃ c : ℝ, c = L + 2 := ⟨_, rfl⟩
  have hC₁3 : 3 ≤ C₁ := by linarith
  obtain ⟨a, ha⟩ : ∃ c : ℝ, c = |Real.log (δ / C₁)| := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := ha ▸ abs_nonneg _
  obtain ⟨B₀', hB₀'⟩ : ∃ c : ℝ, c = max B₀ 0 := ⟨_, rfl⟩
  obtain ⟨C₂', hC₂'⟩ : ∃ c : ℝ, c = max C₂ 0 := ⟨_, rfl⟩
  have hB₀'0 : 0 ≤ B₀' := hB₀' ▸ le_max_right _ _
  have hC₂'0 : 0 ≤ C₂' := hC₂' ▸ le_max_right _ _
  have hC₂C₂' : C₂ ≤ C₂' := hC₂' ▸ le_max_left _ _
  have hlog4 : 0 ≤ Real.log (4 * C₁ ^ 2) := Real.log_nonneg (by nlinarith)
  obtain ⟨E, hE⟩ : ∃ c : ℝ, c = (1 + c₀) * (2 * Real.log (4 * C₁ ^ 2) * (B₀' + C₂')) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ c : ℝ, c = max (max E L) (C₂' + |B₁| + 1) := ⟨_, rfl⟩
  have hCE : E ≤ C := hC ▸ (le_max_left _ _).trans (le_max_left _ _)
  have hCL : L ≤ C := hC ▸ (le_max_right _ _).trans (le_max_left _ _)
  have hCB : C₂' + |B₁| + 1 ≤ C := hC ▸ le_max_right _ _
  have hC0 : 0 ≤ C := by linarith [abs_nonneg B₁]
  have hC₁2 : 0 < C₁ + 2 := by linarith
  refine ⟨C, min (min t₂ δ₁) (min (δ / (C₁ + 2)) (Real.exp (-(Real.exp 1 + 2 * a)))),
    lt_min (lt_min ht₂ hδ₁) (lt_min (div_pos hδ hC₁2) (Real.exp_pos _)), ?_⟩
  intro t ht ht₀ K hK
  simp only [lt_min_iff] at ht₀
  obtain ⟨⟨htt₂, htδ₁⟩, htδ, hte⟩ := ht₀
  have hCt : t * (C₁ + 2) < δ := (lt_div_iff₀ hC₁2).1 htδ
  have hCt' : t * (C₁ + 2) = C₁ * t + 2 * t := by ring
  have hC₁t : C₁ * t ≤ δ := by linarith
  have hC₁tlt : C₁ * t < δ := by linarith
  have htLt : t ≤ L * t := le_mul_of_one_le_left ht.le hL
  have hLt : L * t ≤ C₁ * t := mul_le_mul_of_nonneg_right (by linarith) ht.le
  have h2t : 2 * t ≤ C₁ * t := mul_le_mul_of_nonneg_right (by linarith) ht.le
  have htC : t ≤ C₁ * t := le_mul_of_one_le_left ht.le (by linarith)
  obtain ⟨hℓa, hlogℓ⟩ := log_inv_facts ht ha0 hte
  have hℓ0 : 0 < Real.log t⁻¹ := by linarith [Real.exp_pos 1]
  have hK0 : 0 ≤ K := le_trans (mul_nonneg hC0 (by linarith)) hK
  have hKB : -K + B₁ ≤ -C₂ * Real.log (Real.log t⁻¹) := by
    have h1' : (C₂' + |B₁| + 1) * Real.log (Real.log t⁻¹) ≤ C * Real.log (Real.log t⁻¹) :=
      mul_le_mul_of_nonneg_right hCB (by linarith)
    have h2' : B₁ ≤ |B₁| * Real.log (Real.log t⁻¹) := by
      have := le_mul_of_one_le_right (abs_nonneg B₁) hlogℓ.le
      linarith [le_abs_self B₁]
    have h3' : C₂ * Real.log (Real.log t⁻¹) ≤ C₂' * Real.log (Real.log t⁻¹) :=
      mul_le_mul_of_nonneg_right hC₂C₂' (by linarith)
    have h4' : (C₂' + |B₁| + 1) * Real.log (Real.log t⁻¹) = C₂' * Real.log (Real.log t⁻¹) +
        |B₁| * Real.log (Real.log t⁻¹) + Real.log (Real.log t⁻¹) := by ring
    have h5' : -C₂ * Real.log (Real.log t⁻¹) = -(C₂ * Real.log (Real.log t⁻¹)) := by ring
    linarith
  have key : ∀ j k : Fin R.N, ∀ x ∈ R.mid j ∩ R.mid k,
      R.phReg ρ K t j x - R.phReg ρ K t k x ≤ E * (Real.log (Real.log t⁻¹) / Real.log t⁻¹) + L * t := by
    intro j k x hx
    obtain ⟨hpj, -⟩ := hVpsh j K
    obtain ⟨hpk, hbk⟩ := hVpsh k K
    have hball : ∀ r, r ≤ δ → closedBall (R.chart k x) r ⊆ V k := fun r hr =>
      (closedBall_subset_closedBall hr).trans (hVball k x hx.2)
    have hballj : closedBall (R.chart j x) t ⊆ V j :=
      (closedBall_subset_closedBall (by linarith : t ≤ δ)).trans (hVball j x hx.1)

    have hi : molli ρ t (R.trunc K j) (R.chart j x) ≤ polyMax (R.trunc K j) (R.chart j x) t :=
      (((mollify_thm D ρ (V j) (R.trunc K j) (hVo j) hpj).1 t ht).2.2.2 (R.chart j x) hballj).2

    have hii : polyMax (R.trunc K j) (R.chart j x) t ≤
        max (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B₁) +
          (R.q j (R.chart j x) - R.q k (R.chart k x)) + L * t :=
      polyMax_le' ht.le fun y hy => hT K j k x hx t ht htδ₁ y hy
    have mono : ∀ s s', 0 ≤ s → s ≤ s' → s' ≤ δ →
        polyMax (R.trunc K k) (R.chart k x) s ≤ polyMax (R.trunc K k) (R.chart k x) s' :=
      fun s s' hs hss' hs' => polyMax_mono' hpk.1 hs hss' (hball _ hs')
    have hlowk := hlow t ht htt₂ K k x hx.2
    have e0 := mono t (L * t) ht.le htLt (by linarith)
    have e1 := mono (L * t) (C₁ * t) (by linarith) hLt hC₁t
    have h4C : 0 < 4 * C₁ := by linarith
    have hq : t / (4 * C₁) ≤ t / 4 := div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith)
    have e2 := mono (t / (4 * C₁)) (t / 4) (by positivity) hq (by linarith)
    have e3 := mono (t / 4) (2 * t) (by positivity) (by linarith) (by linarith)
    have e4 := mono (2 * t) (C₁ * t) (by positivity) h2t hC₁t
    have e5 := mono t (C₁ * t) ht.le htC hC₁t
    have hmax : max (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B₁) =
        polyMax (R.trunc K k) (R.chart k x) (L * t) := max_eq_left (by linarith)
    rw [hmax] at hii

    have hiv := h0 D ρ b (V k) (R.trunc K k) (R.chart k x) t (hVo k) hpk ht
      (hball _ (by linarith)) hb
    rw [← hc₀] at hiv

    have hv := h1 D (V k) (R.trunc K k) (R.chart k x) δ t C₁ (hVo k) hpk (hball δ le_rfl) ht
      (by linarith) hC₁tlt
    have hMδ : polyMax (R.trunc K k) (R.chart k x) δ ≤ B₀' :=
      polyMax_le' hδ.le fun y hy => (hbk y (hVball k x hx.2 hy)).trans
        (max_le (hB₀' ▸ le_max_left _ _) (by linarith))
    have hN : polyMax (R.trunc K k) (R.chart k x) δ - polyMax (R.trunc K k) (R.chart k x) (C₁ * t) ≤
        (B₀' + C₂') * Real.log (Real.log t⁻¹) := by
      have h1' : C₂ * Real.log (Real.log t⁻¹) ≤ C₂' * Real.log (Real.log t⁻¹) :=
        mul_le_mul_of_nonneg_right hC₂C₂' (by linarith)
      have h2' : B₀' ≤ B₀' * Real.log (Real.log t⁻¹) := le_mul_of_one_le_right hB₀'0 hlogℓ.le
      have h3' : -C₂ * Real.log (Real.log t⁻¹) = -(C₂ * Real.log (Real.log t⁻¹)) := by ring
      have h4' : (B₀' + C₂') * Real.log (Real.log t⁻¹) =
          B₀' * Real.log (Real.log t⁻¹) + C₂' * Real.log (Real.log t⁻¹) := by ring
      linarith
    have hden : Real.log t⁻¹ / 2 ≤ Real.log (δ / (C₁ * t)) := by
      rw [show δ / (C₁ * t) = (δ / C₁) * t⁻¹ by field_simp,
        Real.log_mul (div_pos hδ (by linarith)).ne' (inv_pos.2 ht).ne']
      have := neg_abs_le (Real.log (δ / C₁))
      rw [← ha] at this
      linarith [Real.exp_pos 1]
    have hden0 : 0 < Real.log (δ / (C₁ * t)) := by linarith
    have hP : 0 ≤ 2 * Real.log (4 * C₁ ^ 2) * (B₀' + C₂') := by positivity
    have hO : polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
          polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁)) ≤
        2 * Real.log (4 * C₁ ^ 2) * (B₀' + C₂') * (Real.log (Real.log t⁻¹) / Real.log t⁻¹) := by
      refine hv.trans ?_
      rw [div_le_iff₀ hden0]
      calc Real.log (4 * C₁ ^ 2) * (polyMax (R.trunc K k) (R.chart k x) δ -
              polyMax (R.trunc K k) (R.chart k x) (C₁ * t))
          ≤ Real.log (4 * C₁ ^ 2) * ((B₀' + C₂') * Real.log (Real.log t⁻¹)) :=
            mul_le_mul_of_nonneg_left hN hlog4
        _ = 2 * Real.log (4 * C₁ ^ 2) * (B₀' + C₂') *
              (Real.log (Real.log t⁻¹) / Real.log t⁻¹) * (Real.log t⁻¹ / 2) := by
            have hx := div_mul_cancel₀ (Real.log (Real.log t⁻¹)) hℓ0.ne'
            linear_combination (-(Real.log (4 * C₁ ^ 2) * (B₀' + C₂'))) * hx
        _ ≤ 2 * Real.log (4 * C₁ ^ 2) * (B₀' + C₂') *
              (Real.log (Real.log t⁻¹) / Real.log t⁻¹) * Real.log (δ / (C₁ * t)) :=
            mul_le_mul_of_nonneg_left hden (mul_nonneg hP (div_nonneg (by linarith) hℓ0.le))
    have hc : c₀ * (polyMax (R.trunc K k) (R.chart k x) (2 * t) -
          polyMax (R.trunc K k) (R.chart k x) (t / 4)) ≤
        c₀ * (polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
          polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁))) :=
      mul_le_mul_of_nonneg_left (by linarith) hc₀0
    have hfin : (1 + c₀) * (polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
          polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁))) ≤
        E * (Real.log (Real.log t⁻¹) / Real.log t⁻¹) := by
      rw [hE]
      have := mul_le_mul_of_nonneg_left hO (by linarith : (0 : ℝ) ≤ 1 + c₀)
      linarith
    have hsum : polyMax (R.trunc K k) (R.chart k x) (L * t) -
          polyMax (R.trunc K k) (R.chart k x) (2 * t) +
          c₀ * (polyMax (R.trunc K k) (R.chart k x) (2 * t) -
            polyMax (R.trunc K k) (R.chart k x) (t / 4)) ≤
        (1 + c₀) * (polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
          polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁))) := by
      have h' : polyMax (R.trunc K k) (R.chart k x) (L * t) -
          polyMax (R.trunc K k) (R.chart k x) (2 * t) ≤
          polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
            polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁)) := by linarith
      calc _ ≤ (polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
              polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁))) +
            c₀ * (polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
              polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁))) := add_le_add h' hc
        _ = _ := by ring
    simp only [RegChartData.phReg, RegChartData.smoothed]
    linarith
  have hr : 0 ≤ Real.log (Real.log t⁻¹) / Real.log t⁻¹ := div_nonneg (by linarith) hℓ0.le
  intro j k x hx
  have hEC : E * (Real.log (Real.log t⁻¹) / Real.log t⁻¹) + L * t ≤
      C * Real.log (Real.log t⁻¹) / Real.log t⁻¹ + C * t := by
    rw [mul_div_assoc]
    have := mul_le_mul_of_nonneg_right hCE hr
    have := mul_le_mul_of_nonneg_right hCL ht.le
    linarith
  exact abs_sub_le_iff.2 ⟨(key j k x hx).trans hEC, (key k j x ⟨hx.2, hx.1⟩).trans hEC⟩
end ChartComparison
end GroundTheory.Heights₂.Heights.Regular
