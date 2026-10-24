-- Prove2me | solution 1 for YieldPostpone.Pricing.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T06:06:35.311993+00:00
-- url     : https://prove2.me/submissions/83295607-34de-4807-8dbc-852ac7b65f9d

import Mathlib
import Definitions.Def_YieldPostpone_Pricing_Setting
import Definitions.Def_YieldPostpone_Interplay_Setting
import Theorems.Thm_YieldPostpone_Pricing_lemma_1
import Theorems.Thm_YieldPostpone_Pricing_lemma_2
import Theorems.Thm_YieldPostpone_Pricing_lemma_3
import Theorems.Thm_YieldPostpone_Pricing_lemma_4
import Theorems.Thm_YieldPostpone_Pricing_theta_threshold
import Theorems.Thm_YieldPostpone_Pricing_dr_threshold_order
import Theorems.Thm_YieldPostpone_Interplay_lemma_4_at_cDR2

section IP


open YieldPostpone.Interplay

namespace YP3DA

lemma sp_eq (P : Params) (c w Q q : ℝ) :
    supplierProfit P c .DA w Q q =
      P.θ * (w * min Q q) + (1 - P.θ) * (w * min (P.α * Q) q) - c * Q := by
  simp [supplierProfit, E, transfer, delivered, Scenario.byDelivery]

lemma rp_eq (P : Params) (σ : Profile) (w q p : ℝ) :
    retailerProfit P .DA σ w q p =
      P.θ * (p * min (P.a - P.b * p) (min (σ.Q w q) q) - w * min (σ.Q w q) q) +
      (1 - P.θ) * (p * min (P.a - P.b * p) (min (P.α * σ.Q w q) q) -
        w * min (P.α * σ.Q w q) q) := by
  simp [retailerProfit, E, transfer, delivered, salesRev, demand, Scenario.byDelivery,
    Scenario.responsive]

lemma surplus_eq (P : Params) (hb : 0 < P.b) (p X : ℝ) :
    surplus P p X = min (P.a - P.b * p) X * (P.a / P.b - p) -
      (min (P.a - P.b * p) X) ^ 2 / (2 * P.b) := by
  unfold surplus demand
  set m := min (P.a - P.b * p) X
  have hb0 : P.b ≠ 0 := hb.ne'
  have : ∀ t ∈ Set.uIcc (0:ℝ) m, HasDerivAt (fun t => t * (P.a / P.b - p) - t ^ 2 / (2 * P.b))
      ((P.a - t) / P.b - p) t := by
    intro t _
    have h1 := ((hasDerivAt_id t).mul_const (P.a / P.b - p))
    have h2 := ((hasDerivAt_pow 2 t).div_const (2 * P.b))
    refine (h1.sub h2).congr_deriv ?_
    simp only [id, Nat.cast_ofNat]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt this]
  · ring
  · apply Continuous.intervalIntegrable
    fun_prop


/-- Production: low regime, `q` is optimal. -/
lemma prod_low (α θ c w q Q : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hc : 0 < c) (hw : c < w * (α * (1 - θ) + θ)) (hlow : α * (1 - θ) * w ≤ c) (hq : 0 ≤ q) (hQ : 0 ≤ Q) :
    θ * (w * min Q q) + (1 - θ) * (w * min (α * Q) q) - c * Q ≤
      θ * (w * min q q) + (1 - θ) * (w * min (α * q) q) - c * q := by
  have h1θ : 0 < 1 - θ := by linarith
  have hαq : α * q ≤ q := by nlinarith
  rw [min_self, min_eq_left hαq]
  rcases le_total Q q with h | h
  · have hαQ : α * Q ≤ q := by nlinarith
    rw [min_eq_left h, min_eq_left hαQ]
    have : 0 ≤ (w * (α * (1 - θ) + θ) - c) * (q - Q) := by
      apply mul_nonneg <;> linarith
    nlinarith
  · rw [min_eq_right h]
    have hm1 : min (α * Q) q ≤ α * Q := min_le_left _ _
    have hw0 : 0 ≤ w := by
      by_contra hneg
      push Not at hneg
      have : w * (α * (1 - θ) + θ) < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
      linarith
    have h2 : (1 - θ) * (w * min (α * Q) q) ≤ (1 - θ) * (w * (α * Q)) := by
      apply mul_le_mul_of_nonneg_left _ h1θ.le
      exact mul_le_mul_of_nonneg_left hm1 hw0
    have h3 : 0 ≤ (c - α * (1 - θ) * w) * (Q - q) := by
      apply mul_nonneg <;> linarith
    nlinarith

/-- Production: high regime, `q/α` is the unique optimum. -/
lemma prod_high (α θ c w q Q : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hc : 0 < c) (hw : c < w * (α * (1 - θ) + θ)) (hhigh : c < α * (1 - θ) * w)
    (hq : 0 ≤ q) (hQ : 0 ≤ Q) :
    θ * (w * min Q q) + (1 - θ) * (w * min (α * Q) q) - c * Q ≤
      θ * (w * min (q / α) q) + (1 - θ) * (w * min (α * (q / α)) q) - c * (q / α) ∧
    (θ * (w * min Q q) + (1 - θ) * (w * min (α * Q) q) - c * Q =
      θ * (w * min (q / α) q) + (1 - θ) * (w * min (α * (q / α)) q) - c * (q / α) →
      Q = q / α) := by
  have h1θ : 0 < 1 - θ := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hqα : q ≤ q / α := by rw [le_div_iff₀ hα0]; nlinarith
  have hαqα : α * (q / α) = q := by field_simp
  rw [min_eq_right hqα, hαqα, min_self]
  have hw0 : 0 < w := by
    by_contra hneg
    push Not at hneg
    have : α * (1 - θ) * w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  have hk : 0 < α * (1 - θ) * w - c := by linarith
  have hk2 : 0 < w * (α * (1 - θ) + θ) - c := by linarith
  rcases le_total Q q with h | h
  · have hαQ : α * Q ≤ q := by nlinarith
    rw [min_eq_left h, min_eq_left hαQ]
    -- S(q/α) - S(Q) = (wμ-c)(q-Q) + q(1-α)(α(1-θ)w - c)/α
    have key : (θ * (w * q) + (1 - θ) * (w * q) - c * (q / α)) -
        (θ * (w * Q) + (1 - θ) * (w * (α * Q)) - c * Q) =
        (w * (α * (1 - θ) + θ) - c) * (q - Q) + q * (1 - α) * (α * (1 - θ) * w - c) / α := by
      field_simp; ring
    have t1 : 0 ≤ (w * (α * (1 - θ) + θ) - c) * (q - Q) := by
      apply mul_nonneg <;> linarith
    have t2 : 0 ≤ q * (1 - α) * (α * (1 - θ) * w - c) / α := by positivity
    refine ⟨by linarith, fun heq => ?_⟩
    have z1 : (w * (α * (1 - θ) + θ) - c) * (q - Q) = 0 := by linarith
    have z2 : q * (1 - α) * (α * (1 - θ) * w - c) / α = 0 := by linarith
    have hqQ : q - Q = 0 := by
      rcases mul_eq_zero.mp z1 with h' | h'
      · linarith
      · exact h'
    have hq0 : q = 0 := by
      have : q * (1 - α) * (α * (1 - θ) * w - c) = 0 := by
        rw [div_eq_zero_iff] at z2
        rcases z2 with h' | h'
        · exact h'
        · linarith
      rcases mul_eq_zero.mp this with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact h''
        · linarith
      · linarith
    rw [hq0, zero_div]; linarith
  · rw [min_eq_right h]
    rcases le_total Q (q / α) with h' | h'
    · have hαQ : α * Q ≤ q := by
        have := mul_le_mul_of_nonneg_left h' hα0.le
        rwa [hαqα] at this
      rw [min_eq_left hαQ]
      have key : (θ * (w * q) + (1 - θ) * (w * q) - c * (q / α)) -
          (θ * (w * q) + (1 - θ) * (w * (α * Q)) - c * Q) =
          (α * (1 - θ) * w - c) * (q / α - Q) := by
        field_simp; ring
      have t1 : 0 ≤ (α * (1 - θ) * w - c) * (q / α - Q) := by
        apply mul_nonneg <;> linarith
      refine ⟨by linarith, fun heq => ?_⟩
      have z : (α * (1 - θ) * w - c) * (q / α - Q) = 0 := by linarith
      rcases mul_eq_zero.mp z with h'' | h''
      · linarith
      · linarith
    · have hαQ : q ≤ α * Q := by
        have := mul_le_mul_of_nonneg_left h' hα0.le
        rwa [hαqα] at this
      rw [min_eq_right hαQ]
      refine ⟨by nlinarith, fun heq => ?_⟩
      have : c * (Q - q / α) = 0 := by linarith
      rcases mul_eq_zero.mp this with h'' | h''
      · linarith
      · linarith

end YP3DA


open YieldPostpone.Interplay

namespace YP3DA

/-- Retailer in the high regime (full delivery). -/
lemma RH_le (a b w q p : ℝ) (hb : 0 < b) (hw0 : 0 < w) (hwa : b * w < a) (hq : 0 ≤ q)
    (hp : 0 < p) (hpa : b * p < a) :
    p * min (a - b * p) q - w * q ≤ (a - b * w) ^ 2 / (4 * b) ∧
    (p * min (a - b * p) q - w * q = (a - b * w) ^ 2 / (4 * b) →
      q = (a - b * w) / 2 ∧ p = (a + b * w) / (2 * b)) := by
  set m := min (a - b * p) q with hm
  have hm1 : m ≤ a - b * p := min_le_left _ _
  have hm2 : m ≤ q := min_le_right _ _
  have hm0 : 0 ≤ m := le_min (by linarith) hq
  have hV : 0 < (a - b * w) ^ 2 / (4 * b) := by
    have : 0 < a - b * w := by linarith
    positivity
  -- (a-bp)(p-w) ≤ V with gap b (p - pH)^2
  have hgap : (a - b * w) ^ 2 / (4 * b) - (a - b * p) * (p - w) =
      b * (p - (a + b * w) / (2 * b)) ^ 2 := by
    field_simp; ring
  have hsq : 0 ≤ b * (p - (a + b * w) / (2 * b)) ^ 2 := by positivity
  have hwq : w * m ≤ w * q := mul_le_mul_of_nonneg_left hm2 hw0.le
  rcases le_or_gt p w with hpw | hpw
  · have : m * (p - w) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm0 (by linarith)
    have hlt : p * m - w * q < (a - b * w) ^ 2 / (4 * b) := by linarith
    exact ⟨hlt.le, fun h => absurd h hlt.ne⟩
  · have h1 : m * (p - w) ≤ (a - b * p) * (p - w) :=
      mul_le_mul_of_nonneg_right hm1 (by linarith)
    refine ⟨by linarith, fun heq => ?_⟩
    have e1 : w * m = w * q := by linarith
    have e2 : m * (p - w) = (a - b * p) * (p - w) := by linarith
    have e3 : b * (p - (a + b * w) / (2 * b)) ^ 2 = 0 := by linarith
    have hp' : p = (a + b * w) / (2 * b) := by
      have : (p - (a + b * w) / (2 * b)) ^ 2 = 0 := by
        rcases mul_eq_zero.mp e3 with h | h
        · linarith
        · exact h
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      linarith
    have hmq : m = q := mul_left_cancel₀ hw0.ne' e1
    have hmd : m = a - b * p := mul_right_cancel₀ (by linarith : p - w ≠ 0) e2
    refine ⟨?_, hp'⟩
    rw [← hmq, hmd, hp']
    field_simp; ring


set_option maxHeartbeats 4000000 in
/-- Retailer in the low regime (random delivery). -/
lemma RL_le (a b α θ μ s w q p k M : ℝ) (hb : 0 < b) (hα0 : 0 < α) (hα1 : α < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hμ : μ = α * (1 - θ) + θ) (hs0 : 0 < s) (hs : s ^ 2 = μ)
    (hw0 : 0 < w) (hwa : b * w < a) (hq : 0 ≤ q) (hp : 0 < p) (hpa : b * p < a)
    (hk : k = w * μ / α)
    (hM : M = if s * (a - b * w) < a - b * k then (a - b * k) ^ 2 / (4 * b)
      else μ * (a - b * w) ^ 2 / (4 * b)) :
    θ * (p * min (a - b * p) q - w * q) + (1 - θ) * (p * min (a - b * p) (α * q) - w * (α * q))
      ≤ M ∧
    (θ * (p * min (a - b * p) q - w * q) +
        (1 - θ) * (p * min (a - b * p) (α * q) - w * (α * q)) = M →
      (q = (a - b * w) / 2 ∧ p = (a + b * w) / (2 * b) ∧ M = μ * (a - b * w) ^ 2 / (4 * b)) ∨
      (q = (a - b * k) / (2 * α) ∧ p = (a + b * k) / (2 * b) ∧
        M = (a - b * k) ^ 2 / (4 * b) ∧ 0 < a - b * k)) := by
  have h1θ : 0 < 1 - θ := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hαμ : α < μ := by rw [hμ]; nlinarith [mul_pos hθ0 h1α]
  have hμ0 : 0 < μ := by linarith
  have hkα : k * α = w * μ := by rw [hk]; field_simp
  obtain ⟨d, hd⟩ : ∃ x, x = a - b * p := ⟨_, rfl⟩
  rw [← hd]
  have hd0 : 0 < d := by linarith
  obtain ⟨V1, hV1⟩ : ∃ x, x = μ * (a - b * w) ^ 2 / (4 * b) := ⟨_, rfl⟩
  obtain ⟨V2, hV2⟩ : ∃ x, x = (a - b * k) ^ 2 / (4 * b) := ⟨_, rfl⟩
  obtain ⟨E1, hE1⟩ : ∃ x, x = μ * d * (p - w) := ⟨_, rfl⟩
  obtain ⟨E2, hE2⟩ : ∃ x, x = d * (p - k) := ⟨_, rfl⟩
  rw [← hV1, ← hV2]
  rw [← hV1, ← hV2] at hM
  have hV1pos : 0 < V1 := by
    have : 0 < a - b * w := by linarith
    rw [hV1]; positivity
  have gap1 : V1 - E1 = μ * b * (p - (a + b * w) / (2 * b)) ^ 2 := by
    rw [hV1, hE1, hd]; field_simp; ring
  have gap2 : V2 - E2 = b * (p - (a + b * k) / (2 * b)) ^ 2 := by
    rw [hV2, hE2, hd]; field_simp; ring
  have hE1V1 : E1 ≤ V1 := by
    have : 0 ≤ μ * b * (p - (a + b * w) / (2 * b)) ^ 2 := by positivity
    linarith
  have hE2V2 : E2 ≤ V2 := by
    have : 0 ≤ b * (p - (a + b * k) / (2 * b)) ^ 2 := by positivity
    linarith
  have hsaw : 0 < s * (a - b * w) := by
    have : 0 < a - b * w := by linarith
    positivity
  have hsq1 : (s * (a - b * w)) ^ 2 = μ * (a - b * w) ^ 2 := by rw [mul_pow, hs]
  -- comparison of V1 and V2 from the sign of the square-root test
  have hV12 : s * (a - b * w) < a - b * k → V1 < V2 := by
    intro hC
    rw [hV1, hV2]
    apply div_lt_div_of_pos_right _ (by positivity)
    rw [← hsq1]
    exact pow_lt_pow_left₀ hC hsaw.le two_ne_zero
  have hV21 : ¬ (s * (a - b * w) < a - b * k) → 0 ≤ a - b * k → V2 ≤ V1 := by
    intro hC hk0
    push Not at hC
    rw [hV1, hV2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [← hsq1]
    exact pow_le_pow_left₀ hk0 hC 2
  have hV1M : V1 ≤ M := by
    rw [hM]; split_ifs with hC
    · exact (hV12 hC).le
    · exact le_refl _
  have hE2M : E2 ≤ M := by
    rw [hM]; split_ifs with hC
    · exact hE2V2
    · rcases le_or_gt 0 (a - b * k) with hk0 | hk0
      · linarith [hV21 hC hk0]
      · have : p - k < 0 := by
          have : b * p < b * k := by linarith
          have := lt_of_mul_lt_mul_left this hb.le
          linarith
        have : E2 < 0 := by rw [hE2]; exact mul_neg_of_pos_of_neg hd0 this
        linarith
  have hM1 : E1 = M → p = (a + b * w) / (2 * b) ∧ M = V1 := by
    intro h
    have : μ * b * (p - (a + b * w) / (2 * b)) ^ 2 = 0 := by linarith
    have h0 : (p - (a + b * w) / (2 * b)) ^ 2 = 0 := by
      rcases mul_eq_zero.mp this with h' | h'
      · exfalso; have : 0 < μ * b := by positivity
        linarith
      · exact h'
    have := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp h0
    exact ⟨by linarith, by linarith⟩
  have hM2 : E2 = M → p = (a + b * k) / (2 * b) ∧ M = V2 ∧ 0 < a - b * k := by
    intro h
    have hMpos : 0 < M := lt_of_lt_of_le hV1pos hV1M
    have hpk : k < p := by
      by_contra hcon
      push Not at hcon
      have : E2 ≤ 0 := by rw [hE2]; exact mul_nonpos_of_nonneg_of_nonpos hd0.le (by linarith)
      linarith
    have hak : 0 < a - b * k := by
      have : b * k < b * p := mul_lt_mul_of_pos_left hpk hb
      linarith
    have hV2M : V2 ≤ M := by
      rw [hM]; split_ifs with hC
      · exact le_refl _
      · exact hV21 hC hak.le
    have : b * (p - (a + b * k) / (2 * b)) ^ 2 = 0 := by linarith
    have h0 : (p - (a + b * k) / (2 * b)) ^ 2 = 0 := by
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · exact h'
    have := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp h0
    exact ⟨by linarith, by linarith, hak⟩
  have hp12 : (a + b * w) / (2 * b) ≠ (a + b * k) / (2 * b) := by
    intro h
    rw [div_eq_div_iff (by positivity) (by positivity)] at h
    have h2 : (b * (2 * b)) * (w - k) = 0 := by linear_combination h
    have hwk : w = k := by
      rcases mul_eq_zero.mp h2 with h' | h'
      · exfalso; have : 0 < b * (2 * b) := by positivity
        linarith
      · linarith
    have h3 : w * (μ - α) = 0 := by
      rw [← hwk] at hkα
      linear_combination -hkα
    rcases mul_eq_zero.mp h3 with h' | h'
    · linarith
    · linarith
  -- case analysis on q
  rcases le_total q d with hqd | hqd
  · -- q ≤ d : RL = μ q (p - w)
    have hαq : α * q ≤ d := le_trans (mul_le_of_le_one_left hq hα1.le) hqd
    rw [min_eq_right hqd, min_eq_right hαq]
    have hRL : θ * (p * q - w * q) + (1 - θ) * (p * (α * q) - w * (α * q)) =
        μ * q * (p - w) := by rw [hμ]; ring
    rw [hRL]
    rcases le_or_gt p w with hpw | hpw
    · have : μ * q * (p - w) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      have hlt : μ * q * (p - w) < M := by linarith
      exact ⟨hlt.le, fun h => absurd h hlt.ne⟩
    · have hle : μ * q * (p - w) ≤ E1 := by
        rw [hE1]
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left hqd hμ0.le
      refine ⟨by linarith, fun h => Or.inl ?_⟩
      have hE1M : E1 = M := by linarith
      obtain ⟨hp1, hMV⟩ := hM1 hE1M
      have hqd' : q = d := by
        have h2 : μ * (p - w) ≠ 0 := by positivity
        have : q * (μ * (p - w)) = d * (μ * (p - w)) := by rw [hE1] at hE1M; linarith
        exact mul_right_cancel₀ h2 this
      refine ⟨?_, hp1, hMV⟩
      rw [hqd', hd, hp1]; field_simp; ring
  · rcases le_total (α * q) d with hαq | hαq
    · -- d ≤ q ≤ d/α
      rw [min_eq_left hqd, min_eq_right hαq]
      have hid : (1 - α) * d * (θ * (p * d - w * q) + (1 - θ) * (p * (α * q) - w * (α * q))) =
          (d - α * q) * E1 + α * (q - d) * E2 := by
        rw [hE1, hE2]
        have : α * (q - d) * (d * (p - k)) = (q - d) * d * (α * p) - (q - d) * d * (k * α) := by
          ring
        rw [this, hkα, hμ]; ring
      have t1 : (d - α * q) * E1 ≤ (d - α * q) * M :=
        mul_le_mul_of_nonneg_left (le_trans hE1V1 hV1M) (by linarith)
      have t2 : α * (q - d) * E2 ≤ α * (q - d) * M :=
        mul_le_mul_of_nonneg_left hE2M (mul_nonneg hα0.le (by linarith))
      have hpos : 0 < (1 - α) * d := by positivity
      have hle : θ * (p * d - w * q) + (1 - θ) * (p * (α * q) - w * (α * q)) ≤ M := by
        have : (1 - α) * d * (θ * (p * d - w * q) + (1 - θ) * (p * (α * q) - w * (α * q))) ≤
            (1 - α) * d * M := by
          rw [hid]
          have e : (1 - α) * d * M = (d - α * q) * M + α * (q - d) * M := by ring
          rw [e]; linarith
        exact le_of_mul_le_mul_left this hpos
      refine ⟨hle, fun h => ?_⟩
      have z : (d - α * q) * (M - E1) + α * (q - d) * (M - E2) = 0 := by
        have : (1 - α) * d * M = (d - α * q) * E1 + α * (q - d) * E2 := by rw [← h, hid]
        have e : (d - α * q) * (M - E1) + α * (q - d) * (M - E2) =
            (1 - α) * d * M - ((d - α * q) * E1 + α * (q - d) * E2) := by ring
        rw [e, this]; ring
      have z1 : 0 ≤ (d - α * q) * (M - E1) :=
        mul_nonneg (by linarith) (by linarith [le_trans hE1V1 hV1M])
      have z2 : 0 ≤ α * (q - d) * (M - E2) :=
        mul_nonneg (mul_nonneg hα0.le (by linarith)) (by linarith)
      have z1' : (d - α * q) * (M - E1) = 0 := by linarith
      have z2' : α * (q - d) * (M - E2) = 0 := by linarith
      rcases mul_eq_zero.mp z2' with h2 | h2
      · have hqd' : q = d := by
          rcases mul_eq_zero.mp h2 with h3 | h3
          · linarith
          · linarith
        have hE1M : E1 = M := by
          rcases mul_eq_zero.mp z1' with h3 | h3
          · exfalso
            rw [hqd'] at h3
            have : 0 < d - α * d := by have := mul_pos h1α hd0; linarith
            linarith
          · linarith
        obtain ⟨hp1, hMV⟩ := hM1 hE1M
        left
        refine ⟨?_, hp1, hMV⟩
        rw [hqd', hd, hp1]; field_simp; ring
      · have hE2M' : E2 = M := by linarith
        obtain ⟨hp2, hMV, hak⟩ := hM2 hE2M'
        rcases mul_eq_zero.mp z1' with h3 | h3
        · right
          refine ⟨?_, hp2, hMV, hak⟩
          have hq' : q = d / α := by field_simp; linarith
          rw [hq', hd, hp2]; field_simp; ring
        · exfalso
          have hE1M : E1 = M := by linarith
          obtain ⟨hp1, _⟩ := hM1 hE1M
          exact hp12 (hp1.symm.trans hp2)
    · -- q ≥ d/α
      rw [min_eq_left hqd, min_eq_left hαq]
      have hid : α * (θ * (p * d - w * q) + (1 - θ) * (p * d - w * (α * q))) =
          α * E2 - w * μ * (α * q - d) := by
        rw [hE2]
        have : α * (d * (p - k)) = α * d * p - d * (k * α) := by ring
        rw [this, hkα, hμ]; ring
      have hqα : 0 ≤ α * q - d := by linarith
      have hwμ : 0 < w * μ := by positivity
      have t : 0 ≤ w * μ * (α * q - d) := by positivity
      have hle : θ * (p * d - w * q) + (1 - θ) * (p * d - w * (α * q)) ≤ E2 := by
        have : α * (θ * (p * d - w * q) + (1 - θ) * (p * d - w * (α * q))) ≤ α * E2 := by
          linarith
        exact le_of_mul_le_mul_left this hα0
      refine ⟨by linarith, fun h => Or.inr ?_⟩
      have hE2M' : E2 = M := by linarith
      obtain ⟨hp2, hMV, hak⟩ := hM2 hE2M'
      have hq' : α * q = d := by
        have : α * (θ * (p * d - w * q) + (1 - θ) * (p * d - w * (α * q))) = α * E2 := by
          rw [h, hE2M']
        have : w * μ * (α * q - d) = 0 := by linarith
        rcases mul_eq_zero.mp this with h3 | h3
        · linarith
        · linarith
      refine ⟨?_, hp2, hMV, hak⟩
      have : q = d / α := by field_simp; linarith
      rw [this, hd, hp2]; field_simp; ring

end YP3DA


open YieldPostpone.Interplay

namespace YP3DA

lemma wAdm_DA (P : Params) (c w : ℝ) :
    wAdm P c .DA w ↔ c / (μ P) < w ∧ w < P.a / P.b := by
  simp [wAdm, Scenario.byDelivery]

lemma spe_parts (P : Params) (c : ℝ) (σ : Profile) (hσ : IsSPE P c .DA σ) :
    (∀ w q, wAdm P c .DA w → 0 ≤ q →
        0 ≤ σ.Q w q ∧
        (∀ Q', 0 ≤ Q' → supplierProfit P c .DA w Q' q ≤
          supplierProfit P c .DA w (σ.Q w q) q) ∧
        ((∀ Q', 0 ≤ Q' → supplierProfit P c .DA w Q' q ≤
          supplierProfit P c .DA w q q) → σ.Q w q = q)) ∧
    (∀ w, wAdm P c .DA w →
      0 ≤ σ.q w ∧ pAdm P (σ.p w) ∧
      ∀ q' p', 0 ≤ q' → pAdm P p' →
        retailerProfit P .DA σ w q' p' ≤ retailerProfit P .DA σ w (σ.q w) (σ.p w)) ∧
    wAdm P c .DA σ.w ∧
    ∀ w', wAdm P c .DA w' → supplierValue P c .DA σ w' ≤ supplierValue P c .DA σ σ.w := by
  obtain ⟨h1, -, h3, h4, h5⟩ := hσ
  refine ⟨fun w q hw hq => (h1 w q hw hq).1 rfl, fun w hw => ?_, h4, h5⟩
  obtain ⟨a1, a2, a3⟩ := h3 w hw
  exact ⟨a1, a2 rfl, fun q' p' hq hp => a3 q' p' hq (fun _ => hp)⟩

lemma spe_of_parts (P : Params) (c : ℝ) (σ : Profile)
    (h1 : ∀ w q, wAdm P c .DA w → 0 ≤ q →
        0 ≤ σ.Q w q ∧
        (∀ Q', 0 ≤ Q' → supplierProfit P c .DA w Q' q ≤
          supplierProfit P c .DA w (σ.Q w q) q) ∧
        ((∀ Q', 0 ≤ Q' → supplierProfit P c .DA w Q' q ≤
          supplierProfit P c .DA w q q) → σ.Q w q = q))
    (h3 : ∀ w, wAdm P c .DA w →
      0 ≤ σ.q w ∧ pAdm P (σ.p w) ∧
      ∀ q' p', 0 ≤ q' → pAdm P p' →
        retailerProfit P .DA σ w q' p' ≤ retailerProfit P .DA σ w (σ.q w) (σ.p w))
    (h4 : wAdm P c .DA σ.w)
    (h5 : ∀ w', wAdm P c .DA w' → supplierValue P c .DA σ w' ≤ supplierValue P c .DA σ σ.w) :
    IsSPE P c .DA σ := by
  refine ⟨fun w q hw hq => ⟨fun _ => h1 w q hw hq, fun h => by simp [Scenario.byDelivery] at h⟩,
    fun h => by simp [Scenario.responsive] at h, fun w hw => ?_, h4, h5⟩
  obtain ⟨a1, a2, a3⟩ := h3 w hw
  exact ⟨a1, fun _ => a2, fun q' p' hq hp => a3 q' p' hq (hp rfl)⟩

/-- In any SPE the production response is the explicit one. -/
lemma Qchar (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (hσ : IsSPE P c .DA σ) (w q : ℝ) (hw : wAdm P c .DA w) (hq : 0 ≤ q) :
    σ.Q w q = if P.α * (1 - P.θ) * w ≤ c then q else q / P.α := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hμ : (μ P) = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < (μ P) := by
    rw [hμ]
    have : 0 < 1 - P.θ := by linarith
    positivity
  obtain ⟨hw1, -⟩ := (wAdm_DA P c w).mp hw
  have hwμ : c < w * (P.α * (1 - P.θ) + P.θ) := by
    rw [← hμ]; rwa [div_lt_iff₀ hμ0] at hw1
  obtain ⟨hQ0, hQopt, htie⟩ := (spe_parts P c σ hσ).1 w q hw hq
  split_ifs with hlow
  · apply htie
    intro Q' hQ'
    rw [sp_eq, sp_eq]
    exact prod_low P.α P.θ c w q Q' hα0 hα1 hθ0 hθ1 hc hwμ hlow hq hQ'
  · push Not at hlow
    have hα : 0 ≤ q / P.α := by positivity
    have h1 := hQopt (q / P.α) hα
    rw [sp_eq, sp_eq] at h1
    obtain ⟨h2, h3⟩ := prod_high P.α P.θ c w q (σ.Q w q) hα0 hα1 hθ0 hθ1 hc hwμ hlow hq hQ0
    exact h3 (le_antisymm h2 h1)

lemma RP_high (P : Params) (hP : P.Valid) (σ : Profile) (w q p : ℝ) (hq : 0 ≤ q)
    (hQ : σ.Q w q = q / P.α) :
    retailerProfit P .DA σ w q p = p * min (P.a - P.b * p) q - w * q := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  rw [rp_eq, hQ]
  have hqα : q ≤ q / P.α := by rw [le_div_iff₀ hα0]; nlinarith
  have hαqα : P.α * (q / P.α) = q := by field_simp
  rw [min_eq_right hqα, hαqα, min_self]
  ring

lemma RP_low (P : Params) (hP : P.Valid) (σ : Profile) (w q p : ℝ) (hq : 0 ≤ q)
    (hQ : σ.Q w q = q) :
    retailerProfit P .DA σ w q p =
      P.θ * (p * min (P.a - P.b * p) q - w * q) +
        (1 - P.θ) * (p * min (P.a - P.b * p) (P.α * q) - w * (P.α * q)) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  rw [rp_eq, hQ]
  have hαq : P.α * q ≤ q := by nlinarith
  rw [min_self, min_eq_left hαq]

lemma SP_high (P : Params) (hP : P.Valid) (c w q : ℝ) (hq : 0 ≤ q) :
    supplierProfit P c .DA w (q / P.α) q = w * q - c * (q / P.α) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  rw [sp_eq]
  have hqα : q ≤ q / P.α := by rw [le_div_iff₀ hα0]; nlinarith
  have hαqα : P.α * (q / P.α) = q := by field_simp
  rw [min_eq_right hqα, hαqα, min_self]
  ring

lemma SP_low (P : Params) (hP : P.Valid) (c w q : ℝ) (hq : 0 ≤ q) :
    supplierProfit P c .DA w q q = (w * (μ P) - c) * q := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  rw [sp_eq]
  have hαq : P.α * q ≤ q := by nlinarith
  rw [min_self, min_eq_left hαq]
  have hμ : (μ P) = P.α * (1 - P.θ) + P.θ := rfl
  rw [hμ]; ring

lemma cand1_val (a b α θ μ w : ℝ) (hb : 0 < b) (hα0 : 0 < α) (hα1 : α < 1)
    (hμ : μ = α * (1 - θ) + θ) (hwa : b * w < a) :
    θ * ((a + b * w) / (2 * b) * min (a - b * ((a + b * w) / (2 * b))) ((a - b * w) / 2) -
        w * ((a - b * w) / 2)) +
      (1 - θ) * ((a + b * w) / (2 * b) *
        min (a - b * ((a + b * w) / (2 * b))) (α * ((a - b * w) / 2)) -
        w * (α * ((a - b * w) / 2))) = μ * (a - b * w) ^ 2 / (4 * b) := by
  have hd : a - b * ((a + b * w) / (2 * b)) = (a - b * w) / 2 := by field_simp; ring
  have hq0 : 0 ≤ (a - b * w) / 2 := by linarith
  have hαq : α * ((a - b * w) / 2) ≤ (a - b * w) / 2 := by nlinarith
  rw [hd, min_self, min_eq_right hαq, hμ]
  field_simp; ring

lemma cand2_val (a b α θ μ w k : ℝ) (hb : 0 < b) (hα0 : 0 < α) (hα1 : α < 1)
    (hμ : μ = α * (1 - θ) + θ) (hk : k = w * μ / α) (hak : 0 < a - b * k) :
    θ * ((a + b * k) / (2 * b) * min (a - b * ((a + b * k) / (2 * b))) ((a - b * k) / (2 * α)) -
        w * ((a - b * k) / (2 * α))) +
      (1 - θ) * ((a + b * k) / (2 * b) *
        min (a - b * ((a + b * k) / (2 * b))) (α * ((a - b * k) / (2 * α))) -
        w * (α * ((a - b * k) / (2 * α)))) = (a - b * k) ^ 2 / (4 * b) := by
  have hd : a - b * ((a + b * k) / (2 * b)) = (a - b * k) / 2 := by field_simp; ring
  have hαq : α * ((a - b * k) / (2 * α)) = (a - b * k) / 2 := by field_simp
  have hle : (a - b * k) / 2 ≤ (a - b * k) / (2 * α) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  rw [hd, hαq, min_self, min_eq_left hle]
  have hkα : w * μ = k * α := by rw [hk]; field_simp
  have e : θ * ((a + b * k) / (2 * b) * ((a - b * k) / 2) - w * ((a - b * k) / (2 * α))) +
      (1 - θ) * ((a + b * k) / (2 * b) * ((a - b * k) / 2) - w * ((a - b * k) / 2)) =
      (a + b * k) / (2 * b) * ((a - b * k) / 2) -
        (w * (α * (1 - θ) + θ)) * ((a - b * k) / (2 * α)) := by
    field_simp; ring
  rw [e, ← hμ, hkα]
  field_simp; ring

lemma candH_val (a b w : ℝ) (hb : 0 < b) (hwa : b * w < a) :
    (a + b * w) / (2 * b) * min (a - b * ((a + b * w) / (2 * b))) ((a - b * w) / 2) -
      w * ((a - b * w) / 2) = (a - b * w) ^ 2 / (4 * b) := by
  have hd : a - b * ((a + b * w) / (2 * b)) = (a - b * w) / 2 := by field_simp; ring
  rw [hd, min_self]
  field_simp; ring

lemma pAdm_iff (P : Params) (hb : 0 < P.b) (p : ℝ) : pAdm P p ↔ 0 < p ∧ P.b * p < P.a := by
  unfold pAdm
  rw [lt_div_iff₀ hb, mul_comm]

/-- High regime: the retailer's response is forced. -/
lemma resp_high (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (hσ : IsSPE P c .DA σ) (w : ℝ) (hw : wAdm P c .DA w) (hhigh : c < P.α * (1 - P.θ) * w) :
    σ.q w = (P.a - P.b * w) / 2 ∧ σ.p w = (P.a + P.b * w) / (2 * P.b) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : (μ P) = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < (μ P) := by
    rw [hμ]
    have : 0 < 1 - P.θ := by linarith
    positivity
  obtain ⟨hw1, hw2⟩ := (wAdm_DA P c w).mp hw
  have hw0 : 0 < w := lt_trans (div_pos hc hμ0) hw1
  have hwa : P.b * w < P.a := by rwa [lt_div_iff₀ hb, mul_comm] at hw2
  obtain ⟨hq0, hpA, hopt⟩ := (spe_parts P c σ hσ).2.1 w hw
  have hQ : ∀ q, 0 ≤ q → σ.Q w q = q / P.α := by
    intro q hq
    rw [Qchar P hP c hc σ hσ w q hw hq, if_neg (not_le.mpr hhigh)]
  have hq10 : 0 ≤ (P.a - P.b * w) / 2 := by linarith
  have hp1A : pAdm P ((P.a + P.b * w) / (2 * P.b)) := by
    rw [pAdm_iff P hb]
    refine ⟨by positivity, ?_⟩
    have : P.b * ((P.a + P.b * w) / (2 * P.b)) = (P.a + P.b * w) / 2 := by field_simp
    rw [this]; linarith
  have h1 := hopt _ _ hq10 hp1A
  rw [RP_high P hP σ w _ _ hq10 (hQ _ hq10), RP_high P hP σ w _ _ hq0 (hQ _ hq0),
    candH_val P.a P.b w hb hwa] at h1
  obtain ⟨hp0, hpa⟩ := (pAdm_iff P hb _).mp hpA
  obtain ⟨hle, heq⟩ := RH_le P.a P.b w (σ.q w) (σ.p w) hb hw0 hwa hq0 hp0 hpa
  exact heq (le_antisymm hle h1)

noncomputable def kf (P : Params) (w : ℝ) : ℝ := w * (μ P) / P.α

noncomputable def Mf (P : Params) (w : ℝ) : ℝ :=
  if Real.sqrt (μ P) * (P.a - P.b * w) < P.a - P.b * kf P w then
    (P.a - P.b * kf P w) ^ 2 / (4 * P.b)
  else (μ P) * (P.a - P.b * w) ^ 2 / (4 * P.b)

/-- Low regime: the retailer's response is one of the two candidates. -/
lemma resp_low (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (hσ : IsSPE P c .DA σ) (w : ℝ) (hw : wAdm P c .DA w) (hlow : P.α * (1 - P.θ) * w ≤ c) :
    retailerProfit P .DA σ w (σ.q w) (σ.p w) = Mf P w ∧
    ((σ.q w = (P.a - P.b * w) / 2 ∧ σ.p w = (P.a + P.b * w) / (2 * P.b) ∧
        Mf P w = (μ P) * (P.a - P.b * w) ^ 2 / (4 * P.b)) ∨
      (σ.q w = (P.a - P.b * kf P w) / (2 * P.α) ∧
        σ.p w = (P.a + P.b * kf P w) / (2 * P.b) ∧
        Mf P w = (P.a - P.b * kf P w) ^ 2 / (4 * P.b) ∧ 0 < P.a - P.b * kf P w)) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : (μ P) = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < (μ P) := by
    rw [hμ]
    have : 0 < 1 - P.θ := by linarith
    positivity
  have hs0 : 0 < Real.sqrt (μ P) := Real.sqrt_pos.mpr hμ0
  have hs : Real.sqrt (μ P) ^ 2 = (μ P) := Real.sq_sqrt hμ0.le
  obtain ⟨hw1, hw2⟩ := (wAdm_DA P c w).mp hw
  have hw0 : 0 < w := lt_trans (div_pos hc hμ0) hw1
  have hwa : P.b * w < P.a := by rwa [lt_div_iff₀ hb, mul_comm] at hw2
  obtain ⟨hq0, hpA, hopt⟩ := (spe_parts P c σ hσ).2.1 w hw
  have hQ : ∀ q, 0 ≤ q → σ.Q w q = q := by
    intro q hq
    rw [Qchar P hP c hc σ hσ w q hw hq, if_pos hlow]
  have hk : kf P w = w * (μ P) / P.α := rfl
  have hM : Mf P w = if Real.sqrt (μ P) * (P.a - P.b * w) < P.a - P.b * kf P w then
      (P.a - P.b * kf P w) ^ 2 / (4 * P.b) else (μ P) * (P.a - P.b * w) ^ 2 / (4 * P.b) := rfl
  -- value at the candidate
  have hcand : Mf P w ≤ retailerProfit P .DA σ w (σ.q w) (σ.p w) := by
    by_cases hC : Real.sqrt (μ P) * (P.a - P.b * w) < P.a - P.b * kf P w
    · have hak : 0 < P.a - P.b * kf P w := lt_trans (by
        have : 0 < P.a - P.b * w := by linarith
        positivity) hC
      have hq2 : 0 ≤ (P.a - P.b * kf P w) / (2 * P.α) := by positivity
      have hp2A : pAdm P ((P.a + P.b * kf P w) / (2 * P.b)) := by
        rw [pAdm_iff P hb]
        have hk0 : 0 < kf P w := by rw [hk]; positivity
        refine ⟨by positivity, ?_⟩
        have : P.b * ((P.a + P.b * kf P w) / (2 * P.b)) = (P.a + P.b * kf P w) / 2 := by
          field_simp
        rw [this]; linarith
      have h1 := hopt _ _ hq2 hp2A
      rw [RP_low P hP σ w _ _ hq2 (hQ _ hq2),
        cand2_val P.a P.b P.α P.θ (μ P) w (kf P w) hb hα0 hα1 hμ hk hak] at h1
      rw [hM, if_pos hC]; exact h1
    · have hq1 : 0 ≤ (P.a - P.b * w) / 2 := by linarith
      have hp1A : pAdm P ((P.a + P.b * w) / (2 * P.b)) := by
        rw [pAdm_iff P hb]
        refine ⟨by positivity, ?_⟩
        have : P.b * ((P.a + P.b * w) / (2 * P.b)) = (P.a + P.b * w) / 2 := by field_simp
        rw [this]; linarith
      have h1 := hopt _ _ hq1 hp1A
      rw [RP_low P hP σ w _ _ hq1 (hQ _ hq1),
        cand1_val P.a P.b P.α P.θ (μ P) w hb hα0 hα1 hμ hwa] at h1
      rw [hM, if_neg hC]; exact h1
  obtain ⟨hp0, hpa⟩ := (pAdm_iff P hb _).mp hpA
  have hRL := RL_le P.a P.b P.α P.θ (μ P) (Real.sqrt (μ P)) w (σ.q w) (σ.p w) (kf P w) (Mf P w)
    hb hα0 hα1 hθ0 hθ1 hμ hs0 hs hw0 hwa hq0 hp0 hpa hk hM
  rw [RP_low P hP σ w _ _ hq0 (hQ _ hq0)] at hcand ⊢
  obtain ⟨hle, heq⟩ := hRL
  have he := le_antisymm hle hcand
  exact ⟨he, heq he⟩

end YP3DA


open YieldPostpone.Interplay

namespace YP3DA

lemma gH_gap (a b α c w : ℝ) (hb : 0 < b) (hα : 0 < α) :
    (b * c - a * α) ^ 2 / (8 * b * α ^ 2) - (w * ((a - b * w) / 2) - c * ((a - b * w) / 2 / α)) =
      b / 2 * (w - (a / b + c / α) / 2) ^ 2 := by
  field_simp; ring

lemma g1_gap (a b μ c w : ℝ) (hb : 0 < b) (hμ : 0 < μ) :
    (b * c - a * μ) ^ 2 / (8 * b * μ) - (w * μ - c) * ((a - b * w) / 2) =
      b * μ / 2 * (w - (a / b + c / μ) / 2) ^ 2 := by
  field_simp; ring

lemma g2_gap (a b α μ c w k : ℝ) (hb : 0 < b) (hα : 0 < α) (hk : k = w * μ / α) :
    (b * c - a * α) ^ 2 / (8 * b * α ^ 2) - (w * μ - c) * ((a - b * k) / (2 * α)) =
      b / 2 * (k - (a / b + c / α) / 2) ^ 2 := by
  have hkα : w * μ = k * α := by rw [hk]; field_simp
  rw [hkα]
  field_simp; ring

lemma sq_eq_zero_imp (x y : ℝ) (hy : 0 < y) (h : y * x ^ 2 = 0) : x = 0 := by
  rcases mul_eq_zero.mp h with h' | h'
  · linarith
  · exact pow_eq_zero_iff two_ne_zero |>.mp h'

/-- `cDA = a α s (1-s) / (b (s-α))` with `s = √μ`, in multiplied-out form. -/
lemma cDA_eq (P : Params) (hP : P.Valid) :
    cDA P * (P.b * (Real.sqrt (μ P) - P.α)) =
      P.a * P.α * Real.sqrt (μ P) * (1 - Real.sqrt (μ P)) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hμ : (μ P) = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 ≤ (μ P) := by
    rw [hμ]
    have : 0 < 1 - P.θ := by linarith
    positivity
  have hs : Real.sqrt (μ P) ^ 2 = (μ P) := Real.sq_sqrt hμ0
  unfold cDA
  set s := Real.sqrt (μ P)
  have hαθ : P.b * (P.α + P.θ) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, div_eq_iff hαθ]
  rw [hμ] at hs ⊢
  linear_combination (P.a * P.α * P.b * P.α) * hs

/-- Scalar facts about the DA thresholds. -/
lemma DA_scalars (a b α θ s X : ℝ) (ha : 0 < a) (hb : 0 < b) (hα0 : 0 < α) (hα1 : α < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs0 : 0 < s) (hs : s ^ 2 = α * (1 - θ) + θ)
    (hX : X * (b * (s - α)) = a * α * s * (1 - s)) :
    α < s ^ 2 ∧ s < 1 ∧ α < s ∧ X < a * α / b ∧
    (∀ c, c ≤ X → (1 + θ) * (b * c) < a * α * (1 - θ)) ∧
    (∀ c, X < c → a * α * s ^ 2 * (1 - θ) < b * c * (s ^ 2 + θ)) ∧
    (∀ c, X < c → a - b * ((a / b + c / s ^ 2) / 2 * s ^ 2 / α) <
      s * (a - b * ((a / b + c / s ^ 2) / 2))) ∧
    (∀ c, s * (a * α - b * c) - α * (a * s ^ 2 - b * c) = (X - c) * (b * (s - α))) := by
  have h1θ : 0 < 1 - θ := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hαs2 : α < s ^ 2 := by rw [hs]; nlinarith [mul_pos hθ0 h1α]
  have hs21 : s ^ 2 < 1 := by rw [hs]; nlinarith [mul_pos h1θ h1α]
  have hs1 : s < 1 := by nlinarith
  have hαs : α < s := by nlinarith
  have hsα : 0 < s - α := by linarith
  have hbsα : 0 < b * (s - α) := by positivity
  refine ⟨hαs2, hs1, hαs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hb]
    have : X * (b * (s - α)) < a * α * (s - α) := by
      rw [hX]
      have : s * (1 - s) < s - α := by nlinarith
      have := mul_lt_mul_of_pos_left this (by positivity : 0 < a * α)
      linarith
    nlinarith
  · intro c hc
    have hpoly : (1 - α) * ((1 - θ) * (s - α) - (1 + θ) * s * (1 - s)) =
        (1 - s) ^ 2 * (s ^ 2 - α) := by
      linear_combination (2 * s - α - s ^ 2) * hs
    have hbr : 0 < (1 - θ) * (s - α) - (1 + θ) * s * (1 - s) := by
      have : 0 < (1 - s) ^ 2 * (s ^ 2 - α) := by
        have : 0 < 1 - s := by linarith
        have : 0 < s ^ 2 - α := by linarith
        positivity
      rw [← hpoly] at this
      exact pos_of_mul_pos_right this h1α.le
    have hcX : c * (b * (s - α)) ≤ a * α * s * (1 - s) := by
      rw [← hX]; exact mul_le_mul_of_nonneg_right hc hbsα.le
    have : (1 + θ) * (b * c) * (s - α) < a * α * (1 - θ) * (s - α) := by
      have h2 : (1 + θ) * (c * (b * (s - α))) ≤ (1 + θ) * (a * α * s * (1 - s)) :=
        mul_le_mul_of_nonneg_left hcX (by linarith)
      have h3 := mul_lt_mul_of_pos_left hbr (by positivity : 0 < a * α)
      nlinarith
    exact lt_of_mul_lt_mul_right this hsα.le
  · intro c hc
    have hpoly : (1 - α) * (s * (1 - s) * (s ^ 2 + θ) - s ^ 2 * (1 - θ) * (s - α)) =
        s * (1 - s) ^ 2 * (s ^ 2 - α) := by
      linear_combination (-(s * (s ^ 2 - α * s - s + 1))) * hs
    have hbr : 0 ≤ s * (1 - s) * (s ^ 2 + θ) - s ^ 2 * (1 - θ) * (s - α) := by
      have : 0 ≤ s * (1 - s) ^ 2 * (s ^ 2 - α) := by
        have : 0 ≤ s ^ 2 - α := by linarith
        positivity
      rw [← hpoly] at this
      exact nonneg_of_mul_nonneg_right this h1α
    have hcX : a * α * s * (1 - s) < c * (b * (s - α)) := by
      rw [← hX]; exact mul_lt_mul_of_pos_right hc hbsα
    have : a * α * s ^ 2 * (1 - θ) * (s - α) * s < b * c * (s ^ 2 + θ) * (s - α) * s := by
      have h2 := mul_le_mul_of_nonneg_left hbr (by positivity : 0 ≤ a * α)
      have h3 := mul_lt_mul_of_pos_left hcX (by positivity : 0 < s * (s ^ 2 + θ))
      nlinarith
    have hpos : 0 < (s - α) * s := by positivity
    have e1 : a * α * s ^ 2 * (1 - θ) * (s - α) * s = (a * α * s ^ 2 * (1 - θ)) * ((s - α) * s) := by
      ring
    have e2 : b * c * (s ^ 2 + θ) * (s - α) * s = (b * c * (s ^ 2 + θ)) * ((s - α) * s) := by ring
    rw [e1, e2] at this
    exact lt_of_mul_lt_mul_right this hpos.le
  · intro c hc
    have hcX : a * α * s * (1 - s) < c * (b * (s - α)) := by
      rw [← hX]; exact mul_lt_mul_of_pos_right hc hbsα
    have hs2 : 0 < s ^ 2 := by positivity
    -- goal ⇔ b w1 s (s-α) > a α (1-s), w1 = (a/b + c/s²)/2
    have key : a * α * s * (1 - s) ≥ a * s * (2 * α - α * s - s ^ 2) := by
      have : a * s * (α * (1 - s) - (2 * α - α * s - s ^ 2)) ≥ 0 := by
        have : α * (1 - s) - (2 * α - α * s - s ^ 2) = s ^ 2 - α := by ring
        rw [this]; have : 0 ≤ s ^ 2 - α := by linarith
        positivity
      nlinarith
    have e : s * (a - b * ((a / b + c / s ^ 2) / 2)) -
        (a - b * ((a / b + c / s ^ 2) / 2 * s ^ 2 / α)) =
        ((b * c) * (s - α) - a * s * (2 * α - α * s - s ^ 2)) / (2 * s * α) := by
      field_simp; ring
    have : 0 < ((b * c) * (s - α) - a * s * (2 * α - α * s - s ^ 2)) / (2 * s * α) := by
      apply div_pos _ (by positivity)
      nlinarith
    linarith
  · intro c
    linear_combination (-1 : ℝ) * hX

end YP3DA


open YieldPostpone.Interplay

namespace YP3DA

lemma CS_eq (P : Params) (c : ℝ) (σ : Profile) :
    CS P c .DA σ =
      P.θ * surplus P (σ.p σ.w) (min (σ.Q σ.w (σ.q σ.w)) (σ.q σ.w)) +
      (1 - P.θ) * surplus P (σ.p σ.w) (min (P.α * σ.Q σ.w (σ.q σ.w)) (σ.q σ.w)) := by
  simp [CS, E, delivered, Scenario.responsive]

lemma piR_def (P : Params) (c : ℝ) (σ : Profile) :
    piR P c .DA σ = retailerProfit P .DA σ σ.w (σ.q σ.w) (σ.p σ.w) := rfl

lemma piS_def (P : Params) (c : ℝ) (σ : Profile) :
    piS P c .DA σ = supplierValue P c .DA σ σ.w := rfl

lemma SV_def (P : Params) (c : ℝ) (σ : Profile) (w : ℝ) :
    supplierValue P c .DA σ w = supplierProfit P c .DA w (σ.Q w (σ.q w)) (σ.q w) := rfl

/-- Surplus when sales equal `m ≤ demand`, with `a - b p = m'`. -/
lemma surplus_val (P : Params) (hb : 0 < P.b) (p x : ℝ) (hx : x ≤ P.a - P.b * p) :
    surplus P p x = x * ((P.a - P.b * p) / P.b) - x ^ 2 / (2 * P.b) := by
  rw [surplus_eq P hb, min_eq_right hx]
  congr 1
  field_simp

lemma surplus_val' (P : Params) (hb : 0 < P.b) (p x : ℝ) (hx : P.a - P.b * p ≤ x) :
    surplus P p x = (P.a - P.b * p) ^ 2 / (2 * P.b) := by
  rw [surplus_eq P hb, min_eq_left hx]
  field_simp; ring

/-- Outcome in the high regime at `w`, as a function of `w`. -/
lemma outcome_high (P : Params) (hP : P.Valid) (c : ℝ) (σ : Profile)
    (hQ : σ.Q σ.w (σ.q σ.w) = σ.q σ.w / P.α)
    (hq : σ.q σ.w = (P.a - P.b * σ.w) / 2) (hp : σ.p σ.w = (P.a + P.b * σ.w) / (2 * P.b))
    (hwa : P.b * σ.w < P.a) :
    piR P c .DA σ = (P.a - P.b * σ.w) ^ 2 / (4 * P.b) ∧
    CS P c .DA σ = ((P.a - P.b * σ.w) / 2) ^ 2 / (2 * P.b) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hq0 : 0 ≤ σ.q σ.w := by rw [hq]; linarith
  constructor
  · rw [piR_def, RP_high P hP σ _ _ _ hq0 hQ, hq, hp, candH_val _ _ _ hb hwa]
  · rw [CS_eq, hQ]
    have hqα : σ.q σ.w ≤ σ.q σ.w / P.α := by rw [le_div_iff₀ hα0]; nlinarith
    have hαqα : P.α * (σ.q σ.w / P.α) = σ.q σ.w := by field_simp
    rw [min_eq_right hqα, hαqα, min_self]
    have hd : P.a - P.b * σ.p σ.w = σ.q σ.w := by rw [hp, hq]; field_simp; ring
    rw [surplus_val' P hb _ _ (le_of_eq hd), hd, hq]
    ring

lemma outcome_low1 (P : Params) (hP : P.Valid) (c : ℝ) (σ : Profile)
    (hQ : σ.Q σ.w (σ.q σ.w) = σ.q σ.w)
    (hq : σ.q σ.w = (P.a - P.b * σ.w) / 2) (hp : σ.p σ.w = (P.a + P.b * σ.w) / (2 * P.b))
    (hwa : P.b * σ.w < P.a) :
    piR P c .DA σ = (μ P) * (P.a - P.b * σ.w) ^ 2 / (4 * P.b) ∧
    CS P c .DA σ = ((P.a - P.b * σ.w) / 2) ^ 2 / (2 * P.b) *
      (P.α * (2 - P.α) * (1 - P.θ) + P.θ) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : (μ P) = P.α * (1 - P.θ) + P.θ := rfl
  have hq0 : 0 ≤ σ.q σ.w := by rw [hq]; linarith
  constructor
  · rw [piR_def, RP_low P hP σ _ _ _ hq0 hQ, hq, hp,
      cand1_val _ _ _ _ _ _ hb hα0 hα1 hμ hwa]
  · rw [CS_eq, hQ]
    have hαq : P.α * σ.q σ.w ≤ σ.q σ.w := by nlinarith
    rw [min_self, min_eq_left hαq]
    have hd : P.a - P.b * σ.p σ.w = σ.q σ.w := by rw [hp, hq]; field_simp; ring
    rw [surplus_val P hb _ _ (le_of_eq hd.symm), surplus_val P hb _ _ (by rw [hd]; exact hαq), hd,
      hq]
    field_simp; ring

lemma outcome_low2 (P : Params) (hP : P.Valid) (c : ℝ) (σ : Profile) (k : ℝ)
    (hk : k = σ.w * (μ P) / P.α) (hak : 0 < P.a - P.b * k)
    (hQ : σ.Q σ.w (σ.q σ.w) = σ.q σ.w)
    (hq : σ.q σ.w = (P.a - P.b * k) / (2 * P.α)) (hp : σ.p σ.w = (P.a + P.b * k) / (2 * P.b)) :
    piR P c .DA σ = (P.a - P.b * k) ^ 2 / (4 * P.b) ∧
    CS P c .DA σ = ((P.a - P.b * k) / 2) ^ 2 / (2 * P.b) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : (μ P) = P.α * (1 - P.θ) + P.θ := rfl
  have hq0 : 0 ≤ σ.q σ.w := by rw [hq]; positivity
  constructor
  · rw [piR_def, RP_low P hP σ _ _ _ hq0 hQ, hq, hp,
      cand2_val _ _ _ _ _ _ _ hb hα0 hα1 hμ hk hak]
  · rw [CS_eq, hQ]
    have hαq : P.α * σ.q σ.w ≤ σ.q σ.w := by nlinarith
    rw [min_self, min_eq_left hαq]
    have hd : P.a - P.b * σ.p σ.w = (P.a - P.b * k) / 2 := by rw [hp]; field_simp; ring
    have hαq' : P.α * σ.q σ.w = (P.a - P.b * k) / 2 := by rw [hq]; field_simp
    have hle : (P.a - P.b * k) / 2 ≤ σ.q σ.w := by rw [← hαq']; exact hαq
    rw [surplus_val' P hb _ _ (by rw [hd]; exact hle),
      surplus_val' P hb _ _ (by rw [hd, hαq']), hd]
    ring

end YP3DA


open YieldPostpone.Interplay

namespace YP3DA

/-- Supplier value in the high regime. -/
lemma SV_high (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (hσ : IsSPE P c .DA σ) (w : ℝ) (hw : wAdm P c .DA w) (hhigh : c < P.α * (1 - P.θ) * w) :
    supplierValue P c .DA σ w =
      w * ((P.a - P.b * w) / 2) - c * ((P.a - P.b * w) / 2 / P.α) := by
  obtain ⟨hq, -⟩ := resp_high P hP c hc σ hσ w hw hhigh
  have hq0 : 0 ≤ σ.q w := (spe_parts P c σ hσ).2.1 w hw |>.1
  rw [SV_def, Qchar P hP c hc σ hσ w _ hw hq0, if_neg (not_le.mpr hhigh),
    SP_high P hP c w _ hq0, hq]

/-- Supplier value in the low regime. -/
lemma SV_low (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (hσ : IsSPE P c .DA σ) (w : ℝ) (hw : wAdm P c .DA w) (hlow : P.α * (1 - P.θ) * w ≤ c) :
    supplierValue P c .DA σ w = (w * (μ P) - c) * σ.q w := by
  have hq0 : 0 ≤ σ.q w := (spe_parts P c σ hσ).2.1 w hw |>.1
  rw [SV_def, Qchar P hP c hc σ hσ w _ hw hq0, if_pos hlow, SP_low P hP c w _ hq0]

end YP3DA

open YP3DA in
set_option maxHeartbeats 8000000 in

open YP3DA in
set_option maxHeartbeats 8000000 in
theorem DA_at_cDA (P : Params) (hP : P.Valid) (c : ℝ) (hcX : c = cDA P) (σ : Profile)
    (hσ : IsSPE P c .DA σ) :
    (piR P c .DA σ = (P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2) ∧
      piS P c .DA σ = (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) ∧
      CS P c .DA σ = (P.b * c - P.a * P.α) ^ 2 / (32 * P.b * P.α ^ 2)) ∨
    (piR P c .DA σ = (P.b * c - P.a * μ P) ^ 2 / (16 * P.b * μ P) ∧
      piS P c .DA σ = (P.b * c - P.a * μ P) ^ 2 / (8 * P.b * μ P) ∧
      CS P c .DA σ = (P.b * c - P.a * μ P) ^ 2 *
        (P.α * (2 - P.α) * (1 - P.θ) + P.θ) / (32 * P.b * μ P ^ 2)) := by
  have hc0 : 0 < c := by
    obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := id hP
    have hμ0 : 0 < (μ P) := by
      have : (μ P) = P.α * (1 - P.θ) + P.θ := rfl
      rw [this]; have : 0 < 1 - P.θ := by linarith
      positivity
    have hs0 : 0 < (Real.sqrt (μ P)) := Real.sqrt_pos.mpr hμ0
    have hs : (Real.sqrt (μ P)) ^ 2 = (μ P) := Real.sq_sqrt hμ0.le
    obtain ⟨-, hs1, hαs, -⟩ := DA_scalars P.a P.b P.α P.θ (Real.sqrt (μ P)) (cDA P) ha hb hα0
      hα1 hθ0 hθ1 hs0 (by rw [hs]; rfl) (cDA_eq P hP)
    have h := cDA_eq P hP
    have hr : 0 < P.a * P.α * Real.sqrt (μ P) * (1 - Real.sqrt (μ P)) := by
      apply mul_pos (by positivity); linarith
    rw [← h] at hr
    rw [hcX]
    by_contra hneg
    push Not at hneg
    have : cDA P * (P.b * (Real.sqrt (μ P) - P.α)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg (by apply mul_nonneg hb.le; linarith)
    linarith
  have hcμ : c < P.a * μ P / P.b := by
    obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := id hP
    have hμ0 : 0 < (μ P) := by
      have : (μ P) = P.α * (1 - P.θ) + P.θ := rfl
      rw [this]; have : 0 < 1 - P.θ := by linarith
      positivity
    have hs0 : 0 < (Real.sqrt (μ P)) := Real.sqrt_pos.mpr hμ0
    have hs : (Real.sqrt (μ P)) ^ 2 = (μ P) := Real.sq_sqrt hμ0.le
    obtain ⟨hαs2, -, -, hXa, -⟩ := DA_scalars P.a P.b P.α P.θ (Real.sqrt (μ P)) (cDA P) ha hb hα0
      hα1 hθ0 hθ1 hs0 (by rw [hs]; rfl) (cDA_eq P hP)
    rw [hcX]
    rw [hs] at hαs2
    calc cDA P < P.a * P.α / P.b := hXa
      _ ≤ P.a * μ P / P.b := by
        apply div_le_div_of_nonneg_right _ hb.le
        exact mul_le_mul_of_nonneg_left hαs2.le ha.le
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : (μ P) = P.α * (1 - P.θ) + P.θ := rfl
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ0 : 0 < (μ P) := by rw [hμ]; positivity
  have hs0 : 0 < (Real.sqrt (μ P)) := Real.sqrt_pos.mpr hμ0
  have hs : (Real.sqrt (μ P)) ^ 2 = (μ P) := Real.sq_sqrt hμ0.le
  have hX := cDA_eq P hP
  obtain ⟨hαs2, hs1, hαs, hXa, F1, F2a, F2b, F4⟩ :=
    DA_scalars P.a P.b P.α P.θ (Real.sqrt (μ P)) (cDA P) ha hb hα0 hα1 hθ0 hθ1 hs0 (by rw [hs]; exact hμ) hX
  rw [hs] at F2a F2b F4
  have hcμ' : P.b * c < P.a * (μ P) := by rwa [lt_div_iff₀ hb, mul_comm] at hcμ
  have hαμ : P.α < (μ P) := by linarith
  obtain ⟨wH, hwH⟩ : ∃ x, x = (P.a / P.b + c / P.α) / 2 := ⟨_, rfl⟩
  obtain ⟨w1, hw1⟩ : ∃ x, x = (P.a / P.b + c / (μ P)) / 2 := ⟨_, rfl⟩
  obtain ⟨DA1S, hDA1S⟩ : ∃ x, x = (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) := ⟨_, rfl⟩
  obtain ⟨DA2S, hDA2S⟩ : ∃ x, x = (P.b * c - P.a * (μ P)) ^ 2 / (8 * P.b * (μ P)) := ⟨_, rfl⟩
  have hDA2pos : 0 < DA2S := by
    have : P.b * c - P.a * (μ P) ≠ 0 := by linarith
    rw [hDA2S]; positivity
  have hgH : ∀ w, w * ((P.a - P.b * w) / 2) - c * ((P.a - P.b * w) / 2 / P.α) =
      DA1S - P.b / 2 * (w - wH) ^ 2 := by
    intro w
    have := gH_gap P.a P.b P.α c w hb hα0
    rw [hDA1S, hwH]; linarith
  have hg1 : ∀ w, (w * (μ P) - c) * ((P.a - P.b * w) / 2) = DA2S - P.b * (μ P) / 2 * (w - w1) ^ 2 := by
    intro w
    have := g1_gap P.a P.b (μ P) c w hb hμ0
    rw [hDA2S, hw1]; linarith
  have hg2 : ∀ w k, k = w * (μ P) / P.α →
      (w * (μ P) - c) * ((P.a - P.b * k) / (2 * P.α)) = DA1S - P.b / 2 * (k - wH) ^ 2 := by
    intro w k hk
    have := g2_gap P.a P.b P.α (μ P) c w k hb hα0 hk
    rw [hDA1S, hwH]; linarith
  -- admissibility of the candidates
  have hcμa : c / (μ P) < P.a / P.b := by
    rw [div_lt_div_iff₀ hμ0 hb]; linarith
  have hw1adm : wAdm P c .DA w1 := by
    rw [wAdm_DA, hw1]
    constructor <;> linarith
  have hwHadm : c < P.a * P.α / P.b → wAdm P c .DA wH := by
    intro hca
    have hcα : c / P.α < P.a / P.b := by
      rw [div_lt_div_iff₀ hα0 hb]; rw [lt_div_iff₀ hb] at hca; linarith
    have hμα : c / (μ P) < c / P.α := div_lt_div_of_pos_left hc0 hα0 hαμ
    rw [wAdm_DA, hwH]
    constructor <;> linarith
  have hwHhigh : c ≤ (cDA P) → c < P.α * (1 - P.θ) * wH := by
    intro hcX
    have := F1 c hcX
    rw [hwH]
    have e : P.α * (1 - P.θ) * ((P.a / P.b + c / P.α) / 2) - c =
        (P.a * P.α * (1 - P.θ) - (1 + P.θ) * (P.b * c)) / (2 * P.b) := by
      field_simp; ring
    have : 0 < (P.a * P.α * (1 - P.θ) - (1 + P.θ) * (P.b * c)) / (2 * P.b) := by
      apply div_pos _ (by positivity); linarith
    linarith
  have hw1low : (cDA P) < c → P.α * (1 - P.θ) * w1 < c := by
    intro hcX
    have := F2a c hcX
    rw [hw1]
    have e : c - P.α * (1 - P.θ) * ((P.a / P.b + c / (μ P)) / 2) =
        (P.b * c * ((μ P) + P.θ) - P.a * P.α * (μ P) * (1 - P.θ)) / (2 * P.b * (μ P)) := by
      rw [hμ]; field_simp; ring
    have : 0 < (P.b * c * ((μ P) + P.θ) - P.a * P.α * (μ P) * (1 - P.θ)) / (2 * P.b * (μ P)) := by
      apply div_pos _ (by positivity); linarith
    linarith
  have hw1C2 : (cDA P) < c → P.a - P.b * kf P w1 < (Real.sqrt (μ P)) * (P.a - P.b * w1) := by
    intro hcX
    have := F2b c hcX
    rw [hw1]; exact this
  have hcXle : c ≤ cDA P := hcX.le
  have hca : c < P.a * P.α / P.b := lt_of_le_of_lt hcXle hXa
  have hEq : DA1S = DA2S := by
    have hbc : P.b * c < P.a * P.α := by rwa [lt_div_iff₀ hb, mul_comm] at hca
    have key : Real.sqrt (μ P) * (P.a * P.α - P.b * c) = P.α * (P.a * (μ P) - P.b * c) := by
      have := F4 c
      rw [← hcX, sub_self, zero_mul] at this
      linarith
    have hsq : (Real.sqrt (μ P) * (P.a * P.α - P.b * c)) ^ 2 =
        (P.α * (P.a * (μ P) - P.b * c)) ^ 2 := by rw [key]
    rw [mul_pow, mul_pow, hs] at hsq
    rw [hDA1S, hDA2S, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (8 * P.b) * hsq
  obtain ⟨-, -, hwσ, hopt⟩ := spe_parts P c σ hσ
  have hwHa := hwHadm hca
  have hHh := hwHhigh hcXle
  have hSVH : supplierValue P c .DA σ wH = DA1S := by
    rw [SV_high P hP c hc0 σ hσ wH hwHa hHh, hgH wH]; ring
  have hge : DA1S ≤ supplierValue P c .DA σ σ.w := hSVH ▸ hopt wH hwHa
  obtain ⟨hwσ1, hwσ2⟩ := (wAdm_DA P c σ.w).mp hwσ
  have hwa : P.b * σ.w < P.a := by rwa [lt_div_iff₀ hb, mul_comm] at hwσ2
  have hw0 : 0 < σ.w := lt_trans (div_pos hc0 hμ0) hwσ1
  have hq0 : 0 ≤ σ.q σ.w := (spe_parts P c σ hσ).2.1 σ.w hwσ |>.1
  by_cases hreg : P.α * (1 - P.θ) * σ.w ≤ c
  · obtain ⟨hval, hcases⟩ := resp_low P hP c hc0 σ hσ σ.w hwσ hreg
    have hSV := SV_low P hP c hc0 σ hσ σ.w hwσ hreg
    have hQ : σ.Q σ.w (σ.q σ.w) = σ.q σ.w := by
      rw [Qchar P hP c hc0 σ hσ σ.w _ hwσ hq0, if_pos hreg]
    rcases hcases with ⟨hq, hp, hM⟩ | ⟨hq, hp, hM, hak⟩
    · right
      rw [hq, hg1] at hSV
      have hk0 : P.b * (μ P) / 2 * (σ.w - w1) ^ 2 = 0 := by
        have : 0 ≤ P.b * (μ P) / 2 * (σ.w - w1) ^ 2 := by positivity
        linarith
      have hw1' : σ.w = w1 := by
        have := sq_eq_zero_imp (σ.w - w1) (P.b * (μ P) / 2) (by positivity) hk0
        linarith
      obtain ⟨hR, hC⟩ := outcome_low1 P hP c σ hQ hq hp hwa
      refine ⟨?_, ?_, ?_⟩
      · rw [hR, hw1', hw1]; field_simp; ring
      · rw [piS_def, hSV, hk0, sub_zero, hDA2S]
      · rw [hC, hw1', hw1]; field_simp; ring
    · left
      have hk : kf P σ.w = σ.w * (μ P) / P.α := rfl
      rw [hq, hg2 σ.w (kf P σ.w) hk] at hSV
      have hk0 : P.b / 2 * (kf P σ.w - wH) ^ 2 = 0 := by
        have : 0 ≤ P.b / 2 * (kf P σ.w - wH) ^ 2 := by positivity
        linarith
      have hkH : kf P σ.w = wH := by
        have := sq_eq_zero_imp (kf P σ.w - wH) (P.b / 2) (by positivity) hk0
        linarith
      obtain ⟨hR, hC⟩ := outcome_low2 P hP c σ (kf P σ.w) hk hak hQ hq hp
      refine ⟨?_, ?_, ?_⟩
      · rw [hR, hkH, hwH]; field_simp; ring
      · rw [piS_def, hSV, hk0, sub_zero, hDA1S]
      · rw [hC, hkH, hwH]; field_simp; ring
  · left
    push Not at hreg
    obtain ⟨hq, hp⟩ := resp_high P hP c hc0 σ hσ σ.w hwσ hreg
    have hSV := SV_high P hP c hc0 σ hσ σ.w hwσ hreg
    rw [hgH] at hSV
    have hk0 : P.b / 2 * (σ.w - wH) ^ 2 = 0 := by
      have : 0 ≤ P.b / 2 * (σ.w - wH) ^ 2 := by positivity
      linarith
    have hwH' : σ.w = wH := by
      have := sq_eq_zero_imp (σ.w - wH) (P.b / 2) (by positivity) hk0
      linarith
    have hQ : σ.Q σ.w (σ.q σ.w) = σ.q σ.w / P.α := by
      rw [Qchar P hP c hc0 σ hσ σ.w _ hwσ hq0, if_neg (not_le.mpr hreg)]
    obtain ⟨hR, hC⟩ := outcome_high P hP c σ hQ hq hp hwa
    refine ⟨?_, ?_, ?_⟩
    · rw [hR, hwH', hwH]; field_simp; ring
    · rw [piS_def, hSV, hk0, sub_zero, hDA1S]
    · rw [hC, hwH', hwH]; field_simp; ring


open YieldPostpone.Interplay



namespace YP3DR

/-! Pure real-algebra facts for the DR scenario. Throughout
`u = α(1-θ)`, `μ = α(1-θ)+θ`, `σ₂ = α²(1-θ)+θ`. -/

/-- `d * Q(c) = T² - M²` form of the comparison `G3 - G0`. -/
lemma G3_sub_G0 (a b α θ c S : ℝ) (hb : 0 < b) (hα0 : 0 < α) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hS : S ^ 2 = α * (α * (1 - θ) + θ) * (1 - α) * (1 - θ)) :
    (b * c - a * α) ^ 2 / (8 * b * α ^ 2) -
      (α * (1 - θ) + θ) * θ * c * (a * α * (1 - θ) - b * c) /
        (2 * α ^ 2 * (1 - θ) ^ 2 * (α ^ 2 * (1 - θ) + θ)) =
      ((( α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2) * b * c -
          a * α * (1 - θ) * ((α * (1 - θ) + θ) ^ 2 + θ)) ^ 2 -
        (2 * a * α * (1 - θ) * θ * S) ^ 2) /
      (8 * b * α ^ 2 * (1 - θ) ^ 2 * (α ^ 2 * (1 - θ) + θ) *
        (α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2)) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hs2 : 0 < α ^ 2 * (1 - θ) + θ := by positivity
  have hd : 0 < α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2 := by positivity
  have e : (2 * a * α * (1 - θ) * θ * S) ^ 2 =
      4 * a ^ 2 * α ^ 2 * (1 - θ) ^ 2 * θ ^ 2 * (α * (α * (1 - θ) + θ) * (1 - α) * (1 - θ)) := by
    rw [← hS]; ring
  rw [e]
  field_simp
  ring

/-- `T(c₂)² - M² < 0`, the key polynomial fact at `c = c^DR_2`. -/
lemma T_c2 (a b α θ S : ℝ) (ha : 0 < a) (hb : 0 < b) (hα0 : 0 < α) (hα1 : α < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hK : 0 < α^3*(1-θ)^2 - α^2*θ^2 - 2*α^2*θ + 3*α^2 - α*θ^2 + 5*α*θ + θ^2 - θ)
    (hS : S ^ 2 = α * (α * (1 - θ) + θ) * (1 - α) * (1 - θ)) :
    ((α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2) * b *
          (a * α * (α * (1 - θ) + θ) * (1 - θ) / (b * ((α * (1 - θ) + θ) + θ))) -
        a * α * (1 - θ) * ((α * (1 - θ) + θ) ^ 2 + θ)) ^ 2 -
      (2 * a * α * (1 - θ) * θ * S) ^ 2 < 0 := by
  have h1θ : 0 < 1 - θ := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hm : 0 < (α * (1 - θ) + θ) + θ := by positivity
  have e : (2 * a * α * (1 - θ) * θ * S) ^ 2 =
      4 * a ^ 2 * α ^ 2 * (1 - θ) ^ 2 * θ ^ 2 * (α * (α * (1 - θ) + θ) * (1 - α) * (1 - θ)) := by
    rw [← hS]; ring
  rw [e]
  have e2 : (α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2) * b *
          (a * α * (α * (1 - θ) + θ) * (1 - θ) / (b * ((α * (1 - θ) + θ) + θ))) -
        a * α * (1 - θ) * ((α * (1 - θ) + θ) ^ 2 + θ) =
      a * α * (1 - θ) * ((α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2) *
        (α * (1 - θ) + θ) - ((α * (1 - θ) + θ) ^ 2 + θ) * ((α * (1 - θ) + θ) + θ)) /
        ((α * (1 - θ) + θ) + θ) := by
    field_simp
  rw [e2, div_pow, sub_neg, div_lt_iff₀ (by positivity)]
  have hd : 0 < α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2 := by positivity
  have key : 4 * a ^ 2 * α ^ 2 * (1 - θ) ^ 2 * θ ^ 2 * (α * (α * (1 - θ) + θ) * (1 - α) * (1 - θ)) *
        ((α * (1 - θ) + θ) + θ) ^ 2 -
      (a * α * (1 - θ) * ((α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2) *
        (α * (1 - θ) + θ) - ((α * (1 - θ) + θ) ^ 2 + θ) * ((α * (1 - θ) + θ) + θ))) ^ 2 =
      a ^ 2 * α ^ 2 * θ ^ 2 * (1 - α) * (1 - θ) ^ 3 *
        (α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2) *
        (α^3*(1-θ)^2 - α^2*θ^2 - 2*α^2*θ + 3*α^2 - α*θ^2 + 5*α*θ + θ^2 - θ) := by
    ring
  have : 0 < a ^ 2 * α ^ 2 * θ ^ 2 * (1 - α) * (1 - θ) ^ 3 *
        (α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2) *
        (α^3*(1-θ)^2 - α^2*θ^2 - 2*α^2*θ + 3*α^2 - α*θ^2 + 5*α*θ + θ^2 - θ) := by positivity
  linarith

lemma K_pos (α θ : ℝ) (h1 : 9 / 16 ≤ α) (h2 : α < 1) (h3 : 0 < θ) (h4 : θ < 1) :
    0 < α^3*(1-θ)^2 - α^2*θ^2 - 2*α^2*θ + 3*α^2 - α*θ^2 + 5*α*θ + θ^2 - θ := by
  have ha : 0 < α := by linarith
  have hθ' : 0 < 1 - θ := by linarith
  nlinarith [mul_pos ha h3, mul_pos (mul_pos ha ha) hθ', mul_pos (mul_pos ha h3) hθ', mul_pos h3 hθ',
    mul_pos (mul_pos ha ha) h3, mul_pos (mul_pos (mul_pos ha ha) ha) (mul_pos hθ' hθ')]

/-- Case C comparison at `c₂`: `σ₂ (aα - b c₂)² < α² (aμ - b c₂)²`. -/
lemma caseC_c2 (a b α θ : ℝ) (ha : 0 < a) (hb : 0 < b) (hα0 : 0 < α) (hα1 : α < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hK : 0 < α^3*(1-θ)^2 - α^2*θ^2 - 2*α^2*θ + 3*α^2 - α*θ^2 + 5*α*θ + θ^2 - θ) :
    (α ^ 2 * (1 - θ) + θ) *
        (a * α - b * (a * α * (α * (1 - θ) + θ) * (1 - θ) / (b * ((α * (1 - θ) + θ) + θ)))) ^ 2 <
      α ^ 2 * (a * (α * (1 - θ) + θ) -
        b * (a * α * (α * (1 - θ) + θ) * (1 - θ) / (b * ((α * (1 - θ) + θ) + θ)))) ^ 2 := by
  have h1θ : 0 < 1 - θ := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hm : 0 < (α * (1 - θ) + θ) + θ := by positivity
  have e1 : b * (a * α * (α * (1 - θ) + θ) * (1 - θ) / (b * ((α * (1 - θ) + θ) + θ))) =
      a * α * (α * (1 - θ) + θ) * (1 - θ) / ((α * (1 - θ) + θ) + θ) := by
    field_simp
  rw [e1]
  rw [← sub_pos]
  have key : α ^ 2 * (a * (α * (1 - θ) + θ) -
        a * α * (α * (1 - θ) + θ) * (1 - θ) / ((α * (1 - θ) + θ) + θ)) ^ 2 -
      (α ^ 2 * (1 - θ) + θ) *
        (a * α - a * α * (α * (1 - θ) + θ) * (1 - θ) / ((α * (1 - θ) + θ) + θ)) ^ 2 =
      a ^ 2 * α ^ 2 * θ ^ 2 * (1 - α) * (1 - θ) *
        (α^3*(1-θ)^2 - α^2*θ^2 - 2*α^2*θ + 3*α^2 - α*θ^2 + 5*α*θ + θ^2 - θ) /
        ((α * (1 - θ) + θ) + θ) ^ 2 := by
    field_simp
    ring
  rw [key]
  positivity

end YP3DR

open YieldPostpone.Interplay

namespace YP3DR

/-- the comparison of the inflated optimum `G3` with the boundary value `G0` at `w₀`,
governed by `c^DR_1` -/
lemma cdr1_mul (a b α θ μ S D c1 : ℝ) (hb : 0 < b) (hD : 0 < D)
    (h : c1 = a * α * (1 - θ) * (μ ^ 2 + θ - 2 * θ * S) / (b * D)) :
    D * b * c1 = a * α * (1 - θ) * (μ ^ 2 + θ) - 2 * a * α * (1 - θ) * θ * S := by
  rw [h]; field_simp

lemma sqh1 (T M : ℝ) (hM : 0 ≤ M) (h : T ≤ -M) : 0 ≤ T ^ 2 - M ^ 2 := by nlinarith
lemma sqh2 (T M : ℝ) (hM : 0 ≤ M) (h : T < -M) : 0 < T ^ 2 - M ^ 2 := by nlinarith
lemma sqh3 (T M : ℝ) (h1 : -M < T) (h2 : T < M) : T ^ 2 - M ^ 2 < 0 := by nlinarith
lemma sqh4 (T M : ℝ) (hM : 0 ≤ M) (h : T ^ 2 - M ^ 2 < 0) : T < M := by nlinarith

lemma thrAB (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) (c : ℝ) :
    (c ≤ cDR1 P → μ P * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) /
        (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤
        (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2)) ∧
    (c < cDR1 P → μ P * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) /
        (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) <
        (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2)) ∧
    (cDR1 P < c → c < cDR2 P → (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) <
        μ P * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) /
        (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ))) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  have h1α : 0 < 1 - P.α := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  set S := Real.sqrt (P.α * μ P * (1 - P.α) * (1 - P.θ)) with hSdef
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS : S ^ 2 = P.α * (P.α * (1 - P.θ) + P.θ) * (1 - P.α) * (1 - P.θ) := by
    rw [hSdef, Real.sq_sqrt (by positivity), hμ]
  set d := P.α ^ 2 * (1 - P.θ) ^ 3 + 4 * P.α * P.θ * (1 - P.θ) + P.θ * (1 + P.θ) ^ 2 with hd
  have hd0 : 0 < d := by positivity
  have hs2 : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  set M := 2 * P.a * P.α * (1 - P.θ) * P.θ * S with hM
  have hM0 : 0 ≤ M := by positivity
  have key : ∀ c : ℝ, (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) -
      μ P * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) /
        (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) =
      ((d * P.b * c - P.a * P.α * (1 - P.θ) * ((P.α * (1 - P.θ) + P.θ) ^ 2 + P.θ)) ^ 2 - M ^ 2) /
      (8 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) * d) := by
    intro c
    rw [hμ]
    exact G3_sub_G0 P.a P.b P.α P.θ c S hb hα0 hθ0 hθ1 hS
  have hden : 0 < 8 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) * d := by
    positivity
  -- `b d c^DR_1 = aα(1-θ)(μ²+θ) - M`
  have hc1 : d * P.b * cDR1 P = P.a * P.α * (1 - P.θ) * ((P.α * (1 - P.θ) + P.θ) ^ 2 + P.θ) - M := by
    have := cdr1_mul P.a P.b P.α P.θ (μ P) S d (cDR1 P) hb hd0 (by unfold cDR1; rw [← hSdef, ← hd])
    rw [this, hM, hμ]
  have hT2 := T_c2 P.a P.b P.α P.θ S ha hb hα0 hα1 hθ0 hθ1 (K_pos P.α P.θ hα hα1 hθ0 hθ1) hS
  have hc2 : cDR2 P = P.a * P.α * (P.α * (1 - P.θ) + P.θ) * (1 - P.θ) /
      (P.b * ((P.α * (1 - P.θ) + P.θ) + P.θ)) := by
    unfold cDR2; rw [hμ]
  rw [← hd, ← hM, ← hc2] at hT2
  refine ⟨fun h => ?_, fun h => ?_, fun h1 h2 => ?_⟩
  · have hT : d * P.b * c - P.a * P.α * (1 - P.θ) * ((P.α * (1 - P.θ) + P.θ) ^ 2 + P.θ) ≤ -M := by
      have := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ d * P.b)
      linarith
    have : 0 ≤ ((d * P.b * c - P.a * P.α * (1 - P.θ) * ((P.α * (1 - P.θ) + P.θ) ^ 2 + P.θ)) ^ 2 -
        M ^ 2) / (8 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) * d) := by
      exact div_nonneg (sqh1 _ _ hM0 hT) hden.le
    linarith [key c]
  · have hT : d * P.b * c - P.a * P.α * (1 - P.θ) * ((P.α * (1 - P.θ) + P.θ) ^ 2 + P.θ) < -M := by
      have := mul_lt_mul_of_pos_left h (by positivity : (0:ℝ) < d * P.b)
      linarith
    have : 0 < ((d * P.b * c - P.a * P.α * (1 - P.θ) * ((P.α * (1 - P.θ) + P.θ) ^ 2 + P.θ)) ^ 2 -
        M ^ 2) / (8 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) * d) := by
      exact div_pos (sqh2 _ _ hM0 hT) hden
    linarith [key c]
  · have hT1 : -M < d * P.b * c - P.a * P.α * (1 - P.θ) * ((P.α * (1 - P.θ) + P.θ) ^ 2 + P.θ) := by
      have := mul_lt_mul_of_pos_left h1 (by positivity : (0:ℝ) < d * P.b)
      linarith
    have hTc2 : d * P.b * cDR2 P - P.a * P.α * (1 - P.θ) * ((P.α * (1 - P.θ) + P.θ) ^ 2 + P.θ) < M :=
      sqh4 _ _ hM0 hT2
    have hT2' : d * P.b * c - P.a * P.α * (1 - P.θ) * ((P.α * (1 - P.θ) + P.θ) ^ 2 + P.θ) < M := by
      have := mul_lt_mul_of_pos_left h2 (by positivity : (0:ℝ) < d * P.b)
      linarith
    have : ((d * P.b * c - P.a * P.α * (1 - P.θ) * ((P.α * (1 - P.θ) + P.θ) ^ 2 + P.θ)) ^ 2 -
        M ^ 2) / (8 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) * d) < 0 := by
      exact div_neg_of_neg_of_pos (sqh3 _ _ hT1 hT2') hden
    linarith [key c]

/-- above `c^DR_2` (and below `aα/b`), the inflated optimum is below the no-inflation optimum -/
lemma thrC (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) (c : ℝ) (hc2 : cDR2 P ≤ c)
    (hca : P.b * c < P.a * P.α) :
    (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) <
      (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hs2 : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  set s := Real.sqrt (P.α ^ 2 * (1 - P.θ) + P.θ) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hs2
  have hs : s ^ 2 = P.α ^ 2 * (1 - P.θ) + P.θ := Real.sq_sqrt hs2.le
  have hsα : P.α < s := by
    rw [hsdef]; apply Real.lt_sqrt_of_sq_lt
    nlinarith [mul_pos hθ0 (by nlinarith : (0:ℝ) < 1 - P.α ^ 2)]
  have hαμ : P.α < μ P := by rw [hμ]; nlinarith
  have hc2' : cDR2 P = P.a * P.α * (P.α * (1 - P.θ) + P.θ) * (1 - P.θ) /
      (P.b * ((P.α * (1 - P.θ) + P.θ) + P.θ)) := by
    unfold cDR2; rw [hμ]
  have hC := caseC_c2 P.a P.b P.α P.θ ha hb hα0 hα1 hθ0 hθ1 (K_pos P.α P.θ hα hα1 hθ0 hθ1)
  rw [← hc2', ← hμ] at hC
  -- positivity of the two sides at c₂
  have hc2a : P.b * cDR2 P < P.a * P.α := by
    rw [hc2']
    have hm : 0 < (P.α * (1 - P.θ) + P.θ) + P.θ := by positivity
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    have : (P.α * (1 - P.θ) + P.θ) * (1 - P.θ) < (P.α * (1 - P.θ) + P.θ) + P.θ := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left this (mul_pos hb (mul_pos ha hα0))]
  have hA : 0 ≤ s * (P.a * P.α - P.b * cDR2 P) := by
    apply mul_nonneg hs0.le; linarith
  have hB : 0 ≤ P.α * (P.a * μ P - P.b * cDR2 P) := by
    apply mul_nonneg hα0.le; nlinarith [mul_pos ha hα0]
  have hf2 : s * (P.a * P.α - P.b * cDR2 P) < P.α * (P.a * μ P - P.b * cDR2 P) := by
    have h1 : (s * (P.a * P.α - P.b * cDR2 P)) ^ 2 < (P.α * (P.a * μ P - P.b * cDR2 P)) ^ 2 := by
      rw [mul_pow, mul_pow, hs]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 hB h1
  have hf : s * (P.a * P.α - P.b * c) < P.α * (P.a * μ P - P.b * c) := by
    have : (P.b * c - P.b * cDR2 P) * (s - P.α) ≥ 0 :=
      mul_nonneg (by nlinarith) (by linarith)
    nlinarith
  have hA' : 0 ≤ s * (P.a * P.α - P.b * c) := by apply mul_nonneg hs0.le; linarith
  have hsq : (s * (P.a * P.α - P.b * c)) ^ 2 < (P.α * (P.a * μ P - P.b * c)) ^ 2 :=
    pow_lt_pow_left₀ hf hA' (by norm_num)
  rw [mul_pow, mul_pow, hs] at hsq
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have e : (P.b * c - P.a * P.α) ^ 2 = (P.a * P.α - P.b * c) ^ 2 := by ring
  rw [e]
  nlinarith [mul_lt_mul_of_pos_left hsq (by positivity : (0:ℝ) < 8 * P.b)]

end YP3DR

end IP

namespace YP5B
open YieldPostpone

def tP (P : Pricing.Params) : Interplay.Params := ⟨P.a, P.b, P.α, P.θ⟩

def tS : Pricing.Scenario → Interplay.Scenario
  | .OA => .OA
  | .OR => .OR
  | .DA => .DA
  | .DR => .DR

def tσ (σ : Pricing.Profile) : Interplay.Profile := ⟨σ.w, σ.Q, σ.q, σ.p, σ.pr⟩

/-- Back-translation of an Interplay profile; under pay-by-order the production map is
replaced by the identity order `Q w q = q` everywhere. -/
def bσ (k : Pricing.Scenario) (τ : Interplay.Profile) : Pricing.Profile :=
  if k.byDelivery then ⟨τ.w, τ.Q, τ.q, τ.p, τ.pr⟩ else ⟨τ.w, fun _ q => q, τ.q, τ.p, τ.pr⟩

lemma spe_to (P : Pricing.Params) (c : ℝ) (k : Pricing.Scenario) (σ : Pricing.Profile)
    (h : Pricing.IsSPE P c k σ) : Interplay.IsSPE (tP P) c (tS k) (tσ σ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  cases k
  · exact ⟨fun w q _ _ => ⟨fun hd => absurd hd (by decide), fun _ => h1 rfl w q⟩,
      fun hr => absurd hr (by decide), h4, h5, h6⟩
  · exact ⟨fun w q _ _ => ⟨fun hd => absurd hd (by decide), fun _ => h1 rfl w q⟩,
      h3, h4, h5, h6⟩
  · exact ⟨fun w q hw hq => ⟨fun _ => h2 rfl w q hw hq, fun hd => absurd hd (by decide)⟩,
      fun hr => absurd hr (by decide), h4, h5, h6⟩
  · exact ⟨fun w q hw hq => ⟨fun _ => h2 rfl w q hw hq, fun hd => absurd hd (by decide)⟩,
      h3, h4, h5, h6⟩

lemma spe_from (P : Pricing.Params) (c : ℝ) (k : Pricing.Scenario) (τ : Interplay.Profile)
    (h : Interplay.IsSPE (tP P) c (tS k) τ) : Pricing.IsSPE P c k (bσ k τ) := by
  obtain ⟨h1, h3, h4, h5, h6⟩ := h
  cases k
  · -- OA
    have hQ : ∀ w q, Interplay.wAdm (tP P) c .OA w → 0 ≤ q → τ.Q w q = q :=
      fun w q hw hq => (h1 w q hw hq).2 rfl
    have hR : ∀ w q' p', Interplay.wAdm (tP P) c .OA w → 0 ≤ q' →
        Pricing.retailerProfit P .OA (bσ .OA τ) w q' p' =
          Interplay.retailerProfit (tP P) .OA τ w q' p' := by
      intro w q' p' hw hq
      simp only [Pricing.retailerProfit, Interplay.retailerProfit, bσ, hQ w q' hw hq]
      rfl
    refine ⟨fun _ w q => rfl, fun hd => absurd hd (by decide),
      fun hr => absurd hr (by decide), ?_, h5, ?_⟩
    · intro w hw
      obtain ⟨a1, a2, a3⟩ := h4 w hw
      refine ⟨a1, a2, fun q' p' hq hp => ?_⟩
      exact ((hR w q' p' hw hq).trans_le (a3 q' p' hq hp)).trans_eq
        (hR w (τ.q w) (τ.p w) hw a1).symm
    · intro w' hw'
      have e1 : Pricing.supplierValue P c .OA (bσ .OA τ) w' =
          Interplay.supplierValue (tP P) c .OA τ w' := by
        simp only [Pricing.supplierValue, Interplay.supplierValue, bσ,
          hQ w' _ hw' (h4 w' hw').1]
        rfl
      have e2 : Pricing.supplierValue P c .OA (bσ .OA τ) (bσ .OA τ).w =
          Interplay.supplierValue (tP P) c .OA τ τ.w := by
        simp only [Pricing.supplierValue, Interplay.supplierValue, bσ,
          hQ τ.w _ h5 (h4 τ.w h5).1]
        rfl
      rw [e1, e2]; exact h6 w' hw'
  · -- OR
    have hQ : ∀ w q, Interplay.wAdm (tP P) c .OR w → 0 ≤ q → τ.Q w q = q :=
      fun w q hw hq => (h1 w q hw hq).2 rfl
    have hR : ∀ w q' p', Interplay.wAdm (tP P) c .OR w → 0 ≤ q' →
        Pricing.retailerProfit P .OR (bσ .OR τ) w q' p' =
          Interplay.retailerProfit (tP P) .OR τ w q' p' := by
      intro w q' p' hw hq
      simp only [Pricing.retailerProfit, Interplay.retailerProfit, bσ, hQ w q' hw hq]
      rfl
    refine ⟨fun _ w q => rfl, fun hd => absurd hd (by decide),
      h3, ?_, h5, ?_⟩
    · intro w hw
      obtain ⟨a1, a2, a3⟩ := h4 w hw
      refine ⟨a1, a2, fun q' p' hq hp => ?_⟩
      exact ((hR w q' p' hw hq).trans_le (a3 q' p' hq hp)).trans_eq
        (hR w (τ.q w) (τ.p w) hw a1).symm
    · intro w' hw'
      have e1 : Pricing.supplierValue P c .OR (bσ .OR τ) w' =
          Interplay.supplierValue (tP P) c .OR τ w' := by
        simp only [Pricing.supplierValue, Interplay.supplierValue, bσ,
          hQ w' _ hw' (h4 w' hw').1]
        rfl
      have e2 : Pricing.supplierValue P c .OR (bσ .OR τ) (bσ .OR τ).w =
          Interplay.supplierValue (tP P) c .OR τ τ.w := by
        simp only [Pricing.supplierValue, Interplay.supplierValue, bσ,
          hQ τ.w _ h5 (h4 τ.w h5).1]
        rfl
      rw [e1, e2]; exact h6 w' hw'
  · exact ⟨fun hd => absurd hd (by decide), fun _ w q hw hq => (h1 w q hw hq).1 rfl,
      fun hr => absurd hr (by decide), h4, h5, h6⟩
  · exact ⟨fun hd => absurd hd (by decide), fun _ w q hw hq => (h1 w q hw hq).1 rfl,
      h3, h4, h5, h6⟩

lemma piR_eq (P : Pricing.Params) (c : ℝ) (k : Pricing.Scenario) (σ : Pricing.Profile) :
    Pricing.piR P k σ = Interplay.piR (tP P) c (tS k) (tσ σ) := by
  cases k <;> rfl

lemma piS_eq (P : Pricing.Params) (c : ℝ) (k : Pricing.Scenario) (σ : Pricing.Profile) :
    Pricing.piS P c k σ = Interplay.piS (tP P) c (tS k) (tσ σ) := by
  cases k <;> rfl

lemma CS_eq (P : Pricing.Params) (c : ℝ) (k : Pricing.Scenario) (σ : Pricing.Profile) :
    Pricing.CS P k σ = Interplay.CS (tP P) c (tS k) (tσ σ) := by
  cases k <;> rfl

lemma outcome_eq (P : Pricing.Params) (c : ℝ) (k : Pricing.Scenario) (σ : Pricing.Profile) :
    Pricing.outcome P c k σ = (Interplay.piR (tP P) c (tS k) (tσ σ),
      Interplay.piS (tP P) c (tS k) (tσ σ), Interplay.CS (tP P) c (tS k) (tσ σ)) := by
  simp only [Pricing.outcome, piR_eq P c, piS_eq P c, CS_eq P c]

lemma cOA2_eq (P : Pricing.Params) : Pricing.cOA2 P = Interplay.cOA2 (tP P) := by
  simp only [Pricing.cOA2, Interplay.cOA2, Pricing.what, Interplay.what, Pricing.μ,
    Interplay.μ, tP]

end YP5B

section TM
open YieldPostpone.Pricing

namespace YP5TM

lemma hasDeriv_Theta (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt Theta
      ((2 * x * (4 * x + 3) * (4 * x ^ 4 + 35 * x ^ 3 + 21 * x ^ 2 + 39 * x + 27) +
        3 * (4 * x + 3) * (4 * x ^ 3 - 25 * x ^ 2 - 10 * x + 3) *
          Real.sqrt (x * (3 + 5 * x + x ^ 2))) /
        (Real.sqrt (x * (3 + 5 * x + x ^ 2)) * ((1 - x) * (3 + 4 * x) ^ 2) ^ 2)) x := by
  have hS : 0 < x * (3 + 5 * x + x ^ 2) := by positivity
  set T := Real.sqrt (x * (3 + 5 * x + x ^ 2)) with hT
  have hT0 : 0 < T := Real.sqrt_pos.mpr hS
  have hT2 : T ^ 2 = x * (3 + 5 * x + x ^ 2) := Real.sq_sqrt hS.le
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id' x
  have h1 : HasDerivAt (fun y : ℝ => y * (3 + 5 * y + y ^ 2)) (3 + 10 * x + 3 * x ^ 2) x := by
    have := hid.mul (((hasDerivAt_const x (3:ℝ)).add (hid.const_mul (5:ℝ))).add (hid.pow 2))
    refine this.congr_deriv ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat]
    norm_num
    ring
  have h2 : HasDerivAt (fun y : ℝ => Real.sqrt (y * (3 + 5 * y + y ^ 2)))
      ((3 + 10 * x + 3 * x ^ 2) / (2 * T)) x := h1.sqrt hS.ne'
  have hN : HasDerivAt (fun y : ℝ => y * (3 * (1 - y - 4 * y ^ 2) +
      4 * Real.sqrt (y * (3 + 5 * y + y ^ 2))))
      ((3 * (1 - x - 4 * x ^ 2) + 4 * T) +
        x * (3 * (-1 - 8 * x) + 4 * ((3 + 10 * x + 3 * x ^ 2) / (2 * T)))) x := by
    have := hid.mul (((hasDerivAt_const x (3:ℝ)).mul
      (((hasDerivAt_const x (1:ℝ)).sub hid).sub ((hid.pow 2).const_mul (4:ℝ)))).add
        (h2.const_mul (4:ℝ)))
    refine this.congr_deriv ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat]
    norm_num
    ring
  have hD : HasDerivAt (fun y : ℝ => (1 - y) * (3 + 4 * y) ^ 2)
      (-(3 + 4 * x) ^ 2 + (1 - x) * (8 * (3 + 4 * x))) x := by
    have := ((hasDerivAt_const x (1:ℝ)).sub hid).mul
      (((hasDerivAt_const x (3:ℝ)).add (hid.const_mul (4:ℝ))).pow 2)
    refine this.congr_deriv ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat]
    ring_nf
  have hDn : (1 - x) * (3 + 4 * x) ^ 2 ≠ 0 := by
    have : 0 < 1 - x := by linarith
    positivity
  have hQ : HasDerivAt Theta _ x := hN.div hD hDn
  refine hQ.congr_deriv ?_
  rw [← hT]
  field_simp
  ring_nf
  have hT3 : T ^ 3 = x * (3 + 5 * x + x ^ 2) * T := by rw [pow_succ, hT2]
  have hT4 : T ^ 4 = (x * (3 + 5 * x + x ^ 2)) ^ 2 := by
    rw [show T ^ 4 = (T ^ 2) ^ 2 by ring, hT2]
  simp only [hT2, hT3, hT4]
  ring

theorem Theta_strictMonoOn : StrictMonoOn Theta (Set.Ioo 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · intro x hx
    exact (YP5TM.hasDeriv_Theta x hx.1 hx.2).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    obtain ⟨hx0, hx1⟩ := hx
    rw [(YP5TM.hasDeriv_Theta x hx0 hx1).deriv]
    have hS : 0 < x * (3 + 5 * x + x ^ 2) := by positivity
    set T := Real.sqrt (x * (3 + 5 * x + x ^ 2)) with hT
    have hT0 : 0 < T := Real.sqrt_pos.mpr hS
    have hT2 : T ^ 2 = x * (3 + 5 * x + x ^ 2) := Real.sq_sqrt hS.le
    have hDn : 0 < (1 - x) * (3 + 4 * x) ^ 2 := by
      have : 0 < 1 - x := by linarith
      positivity
    apply div_pos _ (by positivity)
    set A := 2 * x * (4 * x + 3) * (4 * x ^ 4 + 35 * x ^ 3 + 21 * x ^ 2 + 39 * x + 27) with hA
    set B := 3 * (4 * x + 3) * (4 * x ^ 3 - 25 * x ^ 2 - 10 * x + 3) with hB
    have hApos : 0 < A := by positivity
    by_cases hx5 : x ≤ 1 / 5
    · have hB0 : 0 ≤ B := by
        apply mul_nonneg (by positivity)
        nlinarith
      have := mul_nonneg hB0 hT0.le
      linarith
    · push Not at hx5
      have hq : 0 < x ^ 4 + 15 * x ^ 3 + 102 * x ^ 2 + 171 * x - 9 := by nlinarith
      have hdiff : A ^ 2 - B ^ 2 * T ^ 2 =
          x * (x - 1) ^ 2 * (4 * x + 3) ^ 5 * (x ^ 4 + 15 * x ^ 3 + 102 * x ^ 2 + 171 * x - 9) := by
        rw [hT2, hA, hB]; ring
      have hpos : 0 < x * (x - 1) ^ 2 * (4 * x + 3) ^ 5 *
          (x ^ 4 + 15 * x ^ 3 + 102 * x ^ 2 + 171 * x - 9) := by
        have : 0 < (x - 1) ^ 2 := by
          have : x - 1 ≠ 0 := by linarith
          positivity
        positivity
      have hlt : (B * T) ^ 2 < A ^ 2 := by rw [mul_pow]; linarith
      have := abs_lt_of_sq_lt_sq' hlt hApos.le
      linarith [this.1]

end YP5TM

end TM

namespace YP5A

lemma rcmp (X Y k A B : ℝ) (hk : 0 < k) (hA : 0 < A) (hB : 0 < B) :
    X / (k * A) < Y / (k * B) ↔ X * B < Y * A := by
  rw [div_lt_div_iff₀ (mul_pos hk hA) (mul_pos hk hB),
    show X * (k * B) = k * (X * B) by ring, show Y * (k * A) = k * (Y * A) by ring]
  exact ⟨fun h => lt_of_mul_lt_mul_left h hk.le, fun h => mul_lt_mul_of_pos_left h hk⟩

/-- `(α(2-α)(1-θ)+θ) σ₂ < μ²` -/
lemma cs_fac (α θ : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (α * (2 - α) * (1 - θ) + θ) * (α ^ 2 * (1 - θ) + θ) < (α * (1 - θ) + θ) ^ 2 := by
  have e : (α * (1 - θ) + θ) ^ 2 - (α * (2 - α) * (1 - θ) + θ) * (α ^ 2 * (1 - θ) + θ) =
      α ^ 2 * (1 - θ) ^ 2 * (1 - α) ^ 2 := by ring
  have : 0 < α ^ 2 * (1 - θ) ^ 2 * (1 - α) ^ 2 := by
    have : 0 < 1 - θ := by linarith
    have : 0 < 1 - α := by linarith
    positivity
  linarith

/-- DA2 / OA3 versus DR3 / OR2 (all three quantities). -/
lemma cmp_mu (a b α θ c : ℝ) (hb : 0 < b) (hα0 : 0 < α) (hα1 : α < 1) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hc : b * c < a * (α * (1 - θ) + θ)) :
    (a * (α * (1 - θ) + θ) - b * c) ^ 2 / (16 * b * (α * (1 - θ) + θ)) <
      (a * (α * (1 - θ) + θ) - b * c) ^ 2 / (16 * b * (α ^ 2 * (1 - θ) + θ)) ∧
    (a * (α * (1 - θ) + θ) - b * c) ^ 2 / (8 * b * (α * (1 - θ) + θ)) <
      (a * (α * (1 - θ) + θ) - b * c) ^ 2 / (8 * b * (α ^ 2 * (1 - θ) + θ)) ∧
    (a * (α * (1 - θ) + θ) - b * c) ^ 2 * (α * (2 - α) * (1 - θ) + θ) /
        (32 * b * (α * (1 - θ) + θ) ^ 2) <
      (a * (α * (1 - θ) + θ) - b * c) ^ 2 / (32 * b * (α ^ 2 * (1 - θ) + θ)) := by
  have hu : 0 < 1 - θ := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hX : 0 < (a * (α * (1 - θ) + θ) - b * c) ^ 2 := by
    have : a * (α * (1 - θ) + θ) - b * c ≠ 0 := by linarith
    positivity
  have hD : 0 < α ^ 2 * (1 - θ) + θ := by positivity
  have hμ : 0 < α * (1 - θ) + θ := by positivity
  have hDμ : α ^ 2 * (1 - θ) + θ < α * (1 - θ) + θ := by nlinarith [mul_pos (mul_pos hα0 h1α) hu]
  refine ⟨?_, ?_, ?_⟩
  · rw [rcmp _ _ _ _ _ (by positivity) hμ hD]
    exact mul_lt_mul_of_pos_left hDμ hX
  · rw [rcmp _ _ _ _ _ (by positivity) hμ hD]
    exact mul_lt_mul_of_pos_left hDμ hX
  · rw [rcmp _ _ _ _ _ (by positivity) (by positivity) hD]
    have := cs_fac α θ hα0 hα1 hθ0 hθ1
    have h2 := mul_lt_mul_of_pos_left this hX
    have e : (a * (α * (1 - θ) + θ) - b * c) ^ 2 * (α * (2 - α) * (1 - θ) + θ) *
        (α ^ 2 * (1 - θ) + θ) = (a * (α * (1 - θ) + θ) - b * c) ^ 2 *
          ((α * (2 - α) * (1 - θ) + θ) * (α ^ 2 * (1 - θ) + θ)) := by ring
    rw [e]; exact h2

/-- From the core comparison `(aα - bc)² σ₂ < α² (aμ - bc)²`: piece 1 (`α`) below the `σ₂` piece. -/
lemma cmp_al (a b α θ c : ℝ) (hb : 0 < b) (hα0 : 0 < α) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (h : (a * α - b * c) ^ 2 * (α ^ 2 * (1 - θ) + θ) < (a * (α * (1 - θ) + θ) - b * c) ^ 2 * α ^ 2) :
    (a * α - b * c) ^ 2 / (16 * b * α ^ 2) <
      (a * (α * (1 - θ) + θ) - b * c) ^ 2 / (16 * b * (α ^ 2 * (1 - θ) + θ)) ∧
    (a * α - b * c) ^ 2 / (8 * b * α ^ 2) <
      (a * (α * (1 - θ) + θ) - b * c) ^ 2 / (8 * b * (α ^ 2 * (1 - θ) + θ)) ∧
    (a * α - b * c) ^ 2 / (32 * b * α ^ 2) <
      (a * (α * (1 - θ) + θ) - b * c) ^ 2 / (32 * b * (α ^ 2 * (1 - θ) + θ)) := by
  have hu : 0 < 1 - θ := by linarith
  have hD : 0 < α ^ 2 * (1 - θ) + θ := by positivity
  refine ⟨?_, ?_, ?_⟩ <;> rw [rcmp _ _ _ _ _ (by positivity) (by positivity) hD] <;> exact h

/-- the factor `2μ > (1+μ)√σ₂` for `α ≥ 9/16` -/
lemma two_mu (α θ r : ℝ) (hα : 9 / 16 ≤ α) (hα1 : α < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hr0 : 0 ≤ r) (hr2 : r ^ 2 = α ^ 2 * (1 - θ) + θ) :
    (1 + (α * (1 - θ) + θ)) * r < 2 * (α * (1 - θ) + θ) := by
  have hK := YP3DR.K_pos α θ hα hα1 hθ0 hθ1
  have hu : 0 < 1 - θ := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hα0 : 0 < α := by linarith
  have e : (2 * (α * (1 - θ) + θ)) ^ 2 - ((1 + (α * (1 - θ) + θ)) * r) ^ 2 =
      (1 - α) * (1 - θ) *
        (α^3*(1-θ)^2 - α^2*θ^2 - 2*α^2*θ + 3*α^2 - α*θ^2 + 5*α*θ + θ^2 - θ) := by
    linear_combination (-(1 + (α * (1 - θ) + θ)) ^ 2) * hr2
  have hpos : 0 < (1 - α) * (1 - θ) *
      (α^3*(1-θ)^2 - α^2*θ^2 - 2*α^2*θ + 3*α^2 - α*θ^2 + 5*α*θ + θ^2 - θ) := by positivity
  have h2 : ((1 + (α * (1 - θ) + θ)) * r) ^ 2 < (2 * (α * (1 - θ) + θ)) ^ 2 := by linarith
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2

/-- retailer comparison in the middle DR region: `(aα - x)(1-θ)r < 2μ(aα(1-θ) - x)` for
`0 < x < b c^DR_2`. -/
lemma mid_core (a b α θ c r : ℝ) (ha : 0 < a) (hb : 0 < b) (hα : 9 / 16 ≤ α) (hα1 : α < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr0 : 0 ≤ r) (hr2 : r ^ 2 = α ^ 2 * (1 - θ) + θ)
    (hc0 : 0 < c)
    (hc2 : b * c * ((α * (1 - θ) + θ) + θ) < a * α * (α * (1 - θ) + θ) * (1 - θ)) :
    (a * α - b * c) * (1 - θ) * r < 2 * (α * (1 - θ) + θ) * (a * α * (1 - θ) - b * c) := by
  have hu : 0 < 1 - θ := by linarith
  have hα0 : 0 < α := by linarith
  set μ := α * (1 - θ) + θ with hμ
  have hμ0 : 0 < μ := by positivity
  have hμα : α ≤ μ := by rw [hμ]; nlinarith
  set x := b * c with hx
  have hx0 : 0 < x := by positivity
  set x2 := a * α * μ * (1 - θ) / (μ + θ) with hx2
  have hx2e : x2 * (μ + θ) = a * α * μ * (1 - θ) := by
    rw [hx2]; field_simp
  have hxx2 : x < x2 := by
    rw [hx2, lt_div_iff₀ (by positivity)]; linarith
  have hD : r ^ 2 < μ := by rw [hr2, hμ]; nlinarith [mul_pos (mul_pos hα0 (by linarith : (0:ℝ) < 1 - α)) hu]
  have hr_lt : r < 2 * μ := by
    have h1 : r ^ 2 < (2 * μ) ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h1
  have htm := two_mu α θ r hα hα1 hθ0 hθ1 hr0 hr2
  rw [← hμ] at htm
  -- f(x) = f0 + m x is affine
  have hf0 : 0 < a * α * (1 - θ) * (2 * μ - r) := by
    apply mul_pos (by positivity); linarith
  have hfx2 : 0 < 2 * μ * (a * α * (1 - θ) - x2) - (a * α - x2) * (1 - θ) * r := by
    have e : (2 * μ * (a * α * (1 - θ) - x2) - (a * α - x2) * (1 - θ) * r) * (μ + θ) =
        a * α * (1 - θ) * θ * (2 * μ - (1 + μ) * r) := by
      have : x2 * (μ + θ) = a * α * μ * (1 - θ) := hx2e
      linear_combination (-(2 * μ) + (1 - θ) * r) * this
    have h1 : 0 < a * α * (1 - θ) * θ * (2 * μ - (1 + μ) * r) := by
      apply mul_pos (by positivity); linarith
    rw [← e] at h1
    exact pos_of_mul_pos_left h1 (by positivity)
  by_cases hm : 0 ≤ (1 - θ) * r - 2 * μ
  · nlinarith [mul_nonneg hx0.le hm]
  · push Not at hm
    nlinarith [mul_pos (sub_pos.2 hxx2) (neg_pos.2 hm)]

end YP5A

open YieldPostpone.Pricing

set_option maxHeartbeats 8000000 in
theorem solution (P : Params) (hP : P.Valid) :
    -- (O): pay-by-order, OA → OR, every α ∈ (0, 1)
    ((∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
        (∃ σ : Profile, IsSPE P c .OA σ) ∧ (∃ σ : Profile, IsSPE P c .OR σ)) ∧
     -- (O)(i)
     (∀ (c : ℝ) (σA σR : Profile), IsSPE P c .OA σA → IsSPE P c .OR σR →
        max (max (cOR P) (cOA2 P)) 0 < c → c < P.a * μ P / P.b →
          piR P .OA σA < piR P .OR σR ∧ piS P c .OA σA < piS P c .OR σR ∧
          CS P .OA σA < CS P .OR σR) ∧
     -- (O)(ii)
     (StrictMonoOn Theta (Set.Ioo 0 1) ∧
      (P.θ < Theta P.α →
        cOA1 P > Ctil P ∧ Ctil P > 0 ∧
        ∀ (c : ℝ) (σA σR : Profile), IsSPE P c .OA σA → IsSPE P c .OR σR →
          Ctil P < c → c < cOA1 P → c < P.a * μ P / P.b →
            piR P .OA σA < piR P .OR σR ∧ piS P c .OA σA < piS P c .OR σR ∧
            CS P .OA σA < CS P .OR σR)) ∧
     -- (O)(iii)
     (0 < cOR P →
        ∀ (c : ℝ) (σA σR : Profile), IsSPE P c .OA σA → IsSPE P c .OR σR →
          0 < c → c < min (cOR P) (cOA1 P) → c < P.a * μ P / P.b →
            piR P .OA σA < piR P .OR σR ∧ piS P c .OR σR < piS P c .OA σA ∧
            CS P .OA σA < CS P .OR σR)) ∧
    -- (D): pay-by-delivery, DA → DR, α ≥ 9/16
    (9 / 16 ≤ P.α →
      (∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
          (∃ σ : Profile, IsSPE P c .DA σ) ∧ (∃ σ : Profile, IsSPE P c .DR σ)) ∧
      ∀ (c : ℝ) (σA σR : Profile), IsSPE P c .DA σA → IsSPE P c .DR σR →
        0 < c → c < P.a * μ P / P.b →
          -- (D)(i)
          (cDR1 P < c →
            piR P .DA σA < piR P .DR σR ∧ piS P c .DA σA < piS P c .DR σR ∧
            CS P .DA σA < CS P .DR σR) ∧
          -- (D)(ii)
          (c < cDR1 P →
            piR P .DA σA = piR P .DR σR ∧ piS P c .DA σA = piS P c .DR σR ∧
            CS P .DA σA = CS P .DR σR)) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hu : 0 < 1 - P.θ := by linarith
  have h1α : 0 < 1 - P.α := by linarith
  have hμdef : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμdef]; positivity
  have hD0 : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  have hcμ : ∀ c, c < P.a * μ P / P.b → P.b * c < P.a * μ P := by
    intro c h; rwa [lt_div_iff₀ hb, mul_comm] at h
  obtain ⟨L1a, L1b, L1⟩ := lemma_1 P hP
  obtain ⟨L2a, L2⟩ := lemma_2 P hP
  have L3 := lemma_3 P hP
  have TT := theta_threshold P hP
  -- outcome extraction
  have outc : ∀ (c : ℝ) (k : Scenario) (σ : Profile) (x y z : ℝ),
      outcome P c k σ = (x, y, z) → piR P k σ = x ∧ piS P c k σ = y ∧ CS P k σ = z := by
    intro c k σ x y z h
    simp only [outcome, Prod.mk.injEq] at h
    exact h
  -- c^OA_1 < aα/b
  have hOA1 : cOA1 P < P.a * P.α / P.b := by
    unfold cOA1
    have hs : 0 ≤ Real.sqrt (μ P) := Real.sqrt_nonneg _
    rw [div_lt_div_iff₀ (by positivity) hb]
    have : μ P - P.α * P.θ - 2 * P.θ * Real.sqrt (μ P) < P.α + P.θ := by
      linarith [mul_nonneg hθ0.le hs, mul_pos hα0 hθ0, hμdef]
    have h2 := mul_lt_mul_of_pos_left this (mul_pos (mul_pos ha hα0) hb)
    linarith [h2]
  refine ⟨⟨fun c hc hc' => ⟨(L1 c hc hc').1, (L2 c hc hc').1⟩, ?_, ⟨YP5TM.Theta_strictMonoOn, ?_⟩,
    ?_⟩, ?_⟩
  · -- (O)(i)
    intro c σA σR hA hR hmax hc'
    have hc0 : 0 < c := lt_of_le_of_lt (le_max_right _ _) hmax
    have hc2 : max 0 (cOA2 P) < c :=
      max_lt hc0 (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hmax)
    have hcR : max 0 (cOR P) < c :=
      max_lt hc0 (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hmax)
    obtain ⟨eA1, eA2, eA3⟩ := outc _ _ _ _ _ _ (((L1 c hc0 hc').2 σA hA).2.2 hc2)
    obtain ⟨eR1, eR2, eR3⟩ := outc _ _ _ _ _ _ (((L2 c hc0 hc').2 σR hR).2 hcR)
    rw [eA1, eA2, eA3, eR1, eR2, eR3]
    exact YP5A.cmp_mu P.a P.b P.α P.θ c hb hα0 hα1 hθ0 hθ1 (hcμ c hc')
  · -- (O)(ii)
    intro hθΘ
    obtain ⟨h1, h2⟩ := TT.1 hθΘ
    refine ⟨h1, h2, fun c σA σR hA hR hc1 hc2 hc' => ?_⟩
    have hc0 : 0 < c := lt_trans h2 hc1
    obtain ⟨eA1, eA2, eA3⟩ := outc _ _ _ _ _ _
      (((L1 c hc0 hc').2 σA hA).1 (lt_max_of_lt_right hc2))
    obtain ⟨eR1, eR2, eR3⟩ := outc _ _ _ _ _ _
      (((L2 c hc0 hc').2 σR hR).2 (max_lt hc0 (lt_trans TT.2 hc1)))
    rw [eA1, eA2, eA3, eR1, eR2, eR3]
    apply YP5A.cmp_al P.a P.b P.α P.θ c hb hα0 hθ0 hθ1
    -- core: (aα - x) r < α (aμ - x) from c > C̃
    set r := Real.sqrt (P.α ^ 2 * (1 - P.θ) + P.θ) with hr
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hr2 : r ^ 2 = P.α ^ 2 * (1 - P.θ) + P.θ := Real.sq_sqrt hD0.le
    have hrα : P.α < r := by
      rw [hr]; apply Real.lt_sqrt_of_sq_lt
      have h1a2 : (0:ℝ) < 1 - P.α ^ 2 := by
        have := mul_pos h1α (by linarith : (0:ℝ) < 1 + P.α)
        linarith [this]
      linarith [mul_pos hθ0 h1a2]
    have hCt : Ctil P * (P.b * (1 + P.α)) = P.a * P.α * (1 - r) := by
      unfold Ctil; rw [← hr]; field_simp
    have hxa : P.b * c < P.a * P.α := by
      have := lt_trans hc2 hOA1
      rwa [lt_div_iff₀ hb, mul_comm] at this
    have hx1 : P.a * P.α * (1 - r) < P.b * c * (1 + P.α) := by
      rw [← hCt]; linarith [mul_lt_mul_of_pos_right hc1 (by positivity : (0:ℝ) < P.b * (1 + P.α))]
    have hcore : (P.a * P.α - P.b * c) * r < P.α * (P.a * μ P - P.b * c) := by
      have e : (P.α * (P.a * μ P - P.b * c) - (P.a * P.α - P.b * c) * r) * (1 + P.α) =
          (r - P.α) * (P.b * c * (1 + P.α) - P.a * P.α * (1 - r)) := by
        rw [hμdef]; linear_combination (-(P.a * P.α)) * hr2
      have : 0 < (r - P.α) * (P.b * c * (1 + P.α) - P.a * P.α * (1 - r)) :=
        mul_pos (by linarith) (by linarith)
      rw [← e] at this
      have := pos_of_mul_pos_left this (by linarith)
      linarith
    have h0 : 0 ≤ (P.a * P.α - P.b * c) * r := mul_nonneg (by linarith) hr0
    have hsq := pow_lt_pow_left₀ hcore h0 two_ne_zero
    rw [mul_pow, mul_pow, hr2] at hsq
    rw [← hμdef]; linarith
  · -- (O)(iii)
    intro hcOR c σA σR hA hR hc0 hcmin hc'
    have hc1 : c < cOR P := lt_of_lt_of_le hcmin (min_le_left _ _)
    have hc2 : c < cOA1 P := lt_of_lt_of_le hcmin (min_le_right _ _)
    obtain ⟨eA1, eA2, eA3⟩ := outc _ _ _ _ _ _
      (((L1 c hc0 hc').2 σA hA).1 (lt_max_of_lt_right hc2))
    obtain ⟨eR1, eR2, eR3⟩ := outc _ _ _ _ _ _
      (((L2 c hc0 hc').2 σR hR).1 (lt_max_of_lt_right hc1))
    rw [eA1, eA2, eA3, eR1, eR2, eR3]
    have hx0 : 0 < P.b * c := mul_pos hb hc0
    -- c^OR < aα(1-θ)/b
    have hORu : P.b * cOR P < P.a * P.α * (1 - P.θ) := by
      have hv : 0 ≤ Real.sqrt (P.α ^ 2 + P.θ / (1 - P.θ)) := Real.sqrt_nonneg _
      unfold cOR
      have e : P.b * (P.a / P.b * P.α * (1 - P.θ) *
          ((1 - P.α) - Real.sqrt (P.α ^ 2 + P.θ / (1 - P.θ)))) =
          P.a * P.α * (1 - P.θ) * ((1 - P.α) - Real.sqrt (P.α ^ 2 + P.θ / (1 - P.θ))) := by
        field_simp
      rw [e]
      have : (1 - P.α) - Real.sqrt (P.α ^ 2 + P.θ / (1 - P.θ)) < 1 := by linarith
      have hp : 0 < P.a * P.α * (1 - P.θ) := by positivity
      linarith [mul_lt_mul_of_pos_left this hp, mul_one (P.a * P.α * (1 - P.θ))]
    have hxu : P.b * c < P.a * P.α * (1 - P.θ) := by
      have := mul_lt_mul_of_pos_left hc1 hb
      linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [← sub_pos]
      have e : (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 / (16 * P.b * P.α ^ 2 * (1 - P.θ)) +
          P.a ^ 2 * P.θ / (4 * P.b) - (P.a * P.α - P.b * c) ^ 2 / (16 * P.b * P.α ^ 2) =
          P.θ * ((P.b * c) ^ 2 + 3 * P.a ^ 2 * P.α ^ 2 * (1 - P.θ)) /
            (16 * P.b * P.α ^ 2 * (1 - P.θ)) := by
        field_simp; ring
      rw [e]; positivity
    · rw [← sub_pos]
      have e : (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) -
          (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2 * (1 - P.θ)) =
          P.θ * (P.a ^ 2 * P.α ^ 2 * (1 - P.θ) - (P.b * c) ^ 2) /
            (8 * P.b * P.α ^ 2 * (1 - P.θ)) := by
        field_simp; ring
      rw [e]
      apply div_pos _ (by positivity)
      apply mul_pos hθ0
      have h1 : (P.b * c) ^ 2 < (P.a * P.α * (1 - P.θ)) ^ 2 :=
        pow_lt_pow_left₀ hxu hx0.le two_ne_zero
      have h2 : (P.a * P.α * (1 - P.θ)) ^ 2 ≤ P.a ^ 2 * P.α ^ 2 * (1 - P.θ) := by
        have h4 := mul_le_mul_of_nonneg_left (show 1 - P.θ ≤ 1 by linarith) hu.le
        have : (1 - P.θ) ^ 2 ≤ 1 - P.θ := by rw [sq]; linarith
        have h3 : 0 ≤ P.a ^ 2 * P.α ^ 2 := by positivity
        linarith [mul_le_mul_of_nonneg_left this h3,
          show (P.a * P.α * (1 - P.θ)) ^ 2 = P.a ^ 2 * P.α ^ 2 * (1 - P.θ) ^ 2 by ring]
      linarith
    · rw [← sub_pos]
      have e : (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 / (32 * P.b * P.α ^ 2 * (1 - P.θ)) +
          P.a ^ 2 * P.θ / (8 * P.b) - (P.a * P.α - P.b * c) ^ 2 / (32 * P.b * P.α ^ 2) =
          P.θ * ((P.b * c) ^ 2 + 3 * P.a ^ 2 * P.α ^ 2 * (1 - P.θ)) /
            (32 * P.b * P.α ^ 2 * (1 - P.θ)) := by
        field_simp; ring
      rw [e]; positivity
  · -- (D)
    intro hα
    have L4 := lemma_4 P hP hα
    obtain ⟨hd12, hd2A⟩ := dr_threshold_order P hP hα
    refine ⟨fun c hc hc' => ⟨(L3 c hc hc').1, (L4 c hc hc').1⟩,
      fun c σA σR hA hR hc0 hc' => ⟨fun h1 => ?_, fun h1 => ?_⟩⟩
    · -- (D)(i)
      have hx0 : 0 < P.b * c := mul_pos hb hc0
      -- c^DA < aα/b
      have hDAa : P.b * cDA P < P.a * P.α := by
        unfold cDA
        have hs : 0 ≤ Real.sqrt (μ P) := Real.sqrt_nonneg _
        have e : P.b * (P.a * P.α * (μ P - P.θ * Real.sqrt (μ P)) / (P.b * (P.α + P.θ))) =
            P.a * P.α * (μ P - P.θ * Real.sqrt (μ P)) / (P.α + P.θ) := by
          field_simp
        rw [e, div_lt_iff₀ (by positivity)]
        have : μ P - P.θ * Real.sqrt (μ P) < P.α + P.θ := by
          linarith [mul_nonneg hθ0.le hs, mul_pos hα0 hθ0, hμdef]
        exact mul_lt_mul_of_pos_left this (mul_pos ha hα0)
      -- comparison DA piece 1 vs DR piece 3, for cDR2 ≤ c ≤ cDA
      have cmp13 : cDR2 P ≤ c → P.b * c < P.a * P.α →
          (P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2) <
            (P.a * μ P - P.b * c) ^ 2 / (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
          (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) <
            (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
          (P.b * c - P.a * P.α) ^ 2 / (32 * P.b * P.α ^ 2) <
            (P.a * μ P - P.b * c) ^ 2 / (32 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
        intro hc2 hca
        have hC : (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) <
            (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) :=
          YP3DR.thrC (YP5B.tP P) hP hα c hc2 hca
        have hcore := (YP5A.rcmp _ _ _ _ _ (by positivity) (by positivity) hD0).mp hC
        have e : (P.b * c - P.a * P.α) ^ 2 = (P.a * P.α - P.b * c) ^ 2 := by ring
        rw [e] at hcore ⊢
        rw [hμdef] at hcore ⊢
        exact YP5A.cmp_al P.a P.b P.α P.θ c hb hα0 hθ0 hθ1 hcore
      -- DA piece 2 vs DR piece 3
      have cmp23 : (P.b * c - P.a * μ P) ^ 2 / (16 * P.b * μ P) <
            (P.a * μ P - P.b * c) ^ 2 / (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
          (P.b * c - P.a * μ P) ^ 2 / (8 * P.b * μ P) <
            (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
          (P.b * c - P.a * μ P) ^ 2 * (P.α * (2 - P.α) * (1 - P.θ) + P.θ) /
              (32 * P.b * μ P ^ 2) <
            (P.a * μ P - P.b * c) ^ 2 / (32 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
        have e : (P.b * c - P.a * μ P) ^ 2 = (P.a * μ P - P.b * c) ^ 2 := by ring
        rw [e, hμdef]
        exact YP5A.cmp_mu P.a P.b P.α P.θ c hb hα0 hα1 hθ0 hθ1 (by rw [← hμdef]; exact hcμ c hc')
      rcases lt_trichotomy c (cDR2 P) with hlt | heq | hgt
      · -- cDR1 < c < cDR2: DA piece 1, DR piece 2
        obtain ⟨eA1, eA2, eA3⟩ := outc _ _ _ _ _ _
          (((L3 c hc0 hc').2 σA hA).1 (lt_trans hlt hd2A))
        obtain ⟨eR1, eR2, eR3⟩ := outc _ _ _ _ _ _ (((L4 c hc0 hc').2 σR hR).2.1 h1 hlt)
        rw [eA1, eA2, eA3, eR1, eR2, eR3]
        set r := Real.sqrt (P.α ^ 2 * (1 - P.θ) + P.θ) with hr
        have hr0 : 0 ≤ r := Real.sqrt_nonneg _
        have hr2 : r ^ 2 = P.α ^ 2 * (1 - P.θ) + P.θ := Real.sq_sqrt hD0.le
        have hc2' : P.b * c * ((P.α * (1 - P.θ) + P.θ) + P.θ) <
            P.a * P.α * (P.α * (1 - P.θ) + P.θ) * (1 - P.θ) := by
          have e : cDR2 P * (P.b * (μ P + P.θ)) = P.a * P.α * μ P * (1 - P.θ) := by
            unfold cDR2; field_simp
          rw [← hμdef]
          have := mul_lt_mul_of_pos_right hlt (by positivity : (0:ℝ) < P.b * (μ P + P.θ))
          linarith [this, e]
        have hm := YP5A.mid_core P.a P.b P.α P.θ c r ha hb hα hα1 hθ0 hθ1 hr0 hr2 hc0 hc2'
        rw [← hμdef] at hm
        -- x < aα(1-θ)
        have hxu : P.b * c < P.a * P.α * (1 - P.θ) := by
          have hm : 0 < P.α * (1 - P.θ) + P.θ + P.θ := by positivity
          have h3 : P.b * c * (P.α * (1 - P.θ) + P.θ + P.θ) <
              (P.a * P.α * (1 - P.θ)) * (P.α * (1 - P.θ) + P.θ + P.θ) := by
            have := mul_lt_mul_of_pos_left
              (show P.α * (1 - P.θ) + P.θ < P.α * (1 - P.θ) + P.θ + P.θ by linarith)
              (show 0 < P.a * P.α * (1 - P.θ) by positivity)
            linarith [hc2']
          exact lt_of_mul_lt_mul_right h3 hm.le
        have hxa : P.b * c < P.a * P.α := by
          have := mul_lt_mul_of_pos_left (show 1 - P.θ < 1 by linarith) (mul_pos ha hα0)
          linarith
        have h0 : 0 ≤ (P.a * P.α - P.b * c) * (1 - P.θ) * r :=
          mul_nonneg (mul_nonneg (by linarith) hu.le) hr0
        have hsq := pow_lt_pow_left₀ hm h0 two_ne_zero
        rw [mul_pow, mul_pow, hr2] at hsq
        have hS := (YP3DR.thrAB (YP5B.tP P) hP hα c).2.2 h1 hlt
        have e : (P.b * c - P.a * P.α) ^ 2 = (P.a * P.α - P.b * c) ^ 2 := by ring
        refine ⟨?_, hS, ?_⟩
        · rw [e, div_lt_div_iff₀ (by positivity) (by positivity)]
          have hk : 0 < 4 * P.b * P.α ^ 2 := by positivity
          linarith [mul_lt_mul_of_pos_left hsq hk]
        · rw [e, div_lt_div_iff₀ (by positivity) (by positivity)]
          have hk : 0 < 8 * P.b * P.α ^ 2 := by positivity
          linarith [mul_lt_mul_of_pos_left hsq hk]
      · -- c = cDR2
        subst heq
        have hres := YieldPostpone.Interplay.lemma_4_at_cDR2 (YP5B.tP P) hP hα (YP5B.tσ σR)
          (YP5B.spe_to P (cDR2 P) .DR σR hR)
        obtain ⟨eR1, eR2, eR3⟩ := hres
        obtain ⟨eA1, eA2, eA3⟩ := outc _ _ _ _ _ _
          (((L3 (cDR2 P) hc0 hc').2 σA hA).1 hd2A)
        have eR1' : piR P .DR σR = (P.a * μ P - P.b * cDR2 P) ^ 2 /
            (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) := eR1
        have eR2' : piS P (cDR2 P) .DR σR = (P.a * μ P - P.b * cDR2 P) ^ 2 /
            (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) := eR2
        have eR3' : CS P .DR σR = (P.a * μ P - P.b * cDR2 P) ^ 2 /
            (32 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) := eR3
        rw [eA1, eA2, eA3, eR1', eR2', eR3']
        have hca : P.b * cDR2 P < P.a * P.α := lt_trans (mul_lt_mul_of_pos_left hd2A hb) hDAa
        exact cmp13 le_rfl hca
      · -- c > cDR2: DR piece 3
        obtain ⟨eR1, eR2, eR3⟩ := outc _ _ _ _ _ _ (((L4 c hc0 hc').2 σR hR).2.2 hgt)
        rcases lt_trichotomy c (cDA P) with hlA | heA | hgA
        · obtain ⟨eA1, eA2, eA3⟩ := outc _ _ _ _ _ _ (((L3 c hc0 hc').2 σA hA).1 hlA)
          rw [eA1, eA2, eA3, eR1, eR2, eR3]
          exact cmp13 hgt.le (lt_trans (mul_lt_mul_of_pos_left hlA hb) hDAa)
        · have hA' := hA
          rw [heA] at hA'
          rcases DA_at_cDA (YP5B.tP P) hP (cDA P) rfl (YP5B.tσ σA)
              (YP5B.spe_to P (cDA P) .DA σA hA') with ⟨eA1, eA2, eA3⟩ | ⟨eA1, eA2, eA3⟩
          · have eA1' : piR P .DA σA = (P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2) := by
              rw [heA]; exact eA1
            have eA2' : piS P c .DA σA = (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) := by
              rw [heA]; exact eA2
            have eA3' : CS P .DA σA = (P.b * c - P.a * P.α) ^ 2 / (32 * P.b * P.α ^ 2) := by
              rw [heA]; exact eA3
            rw [eA1', eA2', eA3', eR1, eR2, eR3]
            exact cmp13 hgt.le (by rw [heA]; exact hDAa)
          · have eA1' : piR P .DA σA = (P.b * c - P.a * μ P) ^ 2 / (16 * P.b * μ P) := by
              rw [heA]; exact eA1
            have eA2' : piS P c .DA σA = (P.b * c - P.a * μ P) ^ 2 / (8 * P.b * μ P) := by
              rw [heA]; exact eA2
            have eA3' : CS P .DA σA = (P.b * c - P.a * μ P) ^ 2 *
                (P.α * (2 - P.α) * (1 - P.θ) + P.θ) / (32 * P.b * μ P ^ 2) := by
              rw [heA]; exact eA3
            rw [eA1', eA2', eA3', eR1, eR2, eR3]
            exact cmp23
        · obtain ⟨eA1, eA2, eA3⟩ := outc _ _ _ _ _ _ (((L3 c hc0 hc').2 σA hA).2 hgA)
          rw [eA1, eA2, eA3, eR1, eR2, eR3]
          exact cmp23
    · -- (D)(ii)
      obtain ⟨eA1, eA2, eA3⟩ := outc _ _ _ _ _ _
        (((L3 c hc0 hc').2 σA hA).1 (lt_trans h1 (lt_trans hd12 hd2A)))
      obtain ⟨eR1, eR2, eR3⟩ := outc _ _ _ _ _ _ (((L4 c hc0 hc').2 σR hR).1 h1)
      rw [eA1, eA2, eA3, eR1, eR2, eR3]
      refine ⟨rfl, by ring, rfl⟩
