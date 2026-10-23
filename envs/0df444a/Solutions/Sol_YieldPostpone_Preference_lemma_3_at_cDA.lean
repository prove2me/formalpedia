-- Prove2me | solution 1 for YieldPostpone.Preference.lemma_3_at_cDA
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T05:33:57.938792+00:00
-- url     : https://prove2.me/submissions/f489d727-a1ae-49fb-b874-e4450e41d256

import Mathlib
import Definitions.Def_YieldPostpone_Preference_Setting
import Definitions.Def_YieldPostpone_Interplay_Setting

section DAH


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
theorem YP3DA.boundary (P : Params) (hP : P.Valid) (c : ℝ) (hc0 : 0 < c)
    (hcμ : c < P.a * μ P / P.b) (hcE : c = cDA P) (σ : Profile) (hσ : IsSPE P c .DA σ) :
    piR P c .DA σ = (P.b * c - P.a * μ P) ^ 2 / (16 * P.b * μ P) ∧
    piS P c .DA σ = (P.b * c - P.a * μ P) ^ 2 / (8 * P.b * μ P) := by
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
  have hca : c < P.a * P.α / P.b := hcE ▸ hXa
  have hwHadm : wAdm P c .DA wH := by
    have hcα : c / P.α < P.a / P.b := by
      rw [div_lt_div_iff₀ hα0 hb]; rw [lt_div_iff₀ hb] at hca; linarith
    have hμα : c / (μ P) < c / P.α := div_lt_div_of_pos_left hc0 hα0 hαμ
    rw [wAdm_DA, hwH]
    constructor <;> linarith
  have hwHhigh : c < P.α * (1 - P.θ) * wH := by
    have := F1 c hcE.le
    rw [hwH]
    have e : P.α * (1 - P.θ) * ((P.a / P.b + c / P.α) / 2) - c =
        (P.a * P.α * (1 - P.θ) - (1 + P.θ) * (P.b * c)) / (2 * P.b) := by
      field_simp; ring
    have : 0 < (P.a * P.α * (1 - P.θ) - (1 + P.θ) * (P.b * c)) / (2 * P.b) := by
      apply div_pos _ (by positivity); linarith
    linarith
  -- at the threshold the two supplier optima coincide
  have hkey : P.α * (P.a * (μ P) - P.b * c) = (Real.sqrt (μ P)) * (P.a * P.α - P.b * c) := by
    have := F4 c
    rw [← hcE, sub_self, zero_mul] at this
    linarith
  have hsq : P.α ^ 2 * (P.b * c - P.a * (μ P)) ^ 2 = (μ P) * (P.b * c - P.a * P.α) ^ 2 := by
    have h2 : (P.α * (P.a * (μ P) - P.b * c)) ^ 2 =
        ((Real.sqrt (μ P)) * (P.a * P.α - P.b * c)) ^ 2 := by rw [hkey]
    rw [mul_pow, mul_pow, hs] at h2
    linear_combination h2
  have hEq : DA1S = DA2S := by
    rw [hDA1S, hDA2S, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (8 * P.b) * hsq.symm
  obtain ⟨-, -, hwσ, hopt⟩ := spe_parts P c σ hσ
  have hSVH : supplierValue P c .DA σ wH = DA1S := by
    rw [SV_high P hP c hc0 σ hσ wH hwHadm hwHhigh, hgH wH]; ring
  have hge : DA1S ≤ supplierValue P c .DA σ σ.w := hSVH ▸ hopt wH hwHadm
  obtain ⟨hwσ1, hwσ2⟩ := (wAdm_DA P c σ.w).mp hwσ
  have hwa : P.b * σ.w < P.a := by rwa [lt_div_iff₀ hb, mul_comm] at hwσ2
  have hq0 : 0 ≤ σ.q σ.w := (spe_parts P c σ hσ).2.1 σ.w hwσ |>.1
  -- the two retailer values agree at the threshold
  have hR12 : (P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2) =
      (P.b * c - P.a * (μ P)) ^ 2 / (16 * P.b * (μ P)) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (16 * P.b) * hsq.symm
  have hS12 : (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) =
      (P.b * c - P.a * (μ P)) ^ 2 / (8 * P.b * (μ P)) := by
    rw [← hDA1S, ← hDA2S, hEq]
  by_cases hreg : P.α * (1 - P.θ) * σ.w ≤ c
  · obtain ⟨hval, hcases⟩ := resp_low P hP c hc0 σ hσ σ.w hwσ hreg
    have hSV := SV_low P hP c hc0 σ hσ σ.w hwσ hreg
    have hQ : σ.Q σ.w (σ.q σ.w) = σ.q σ.w := by
      rw [Qchar P hP c hc0 σ hσ σ.w _ hwσ hq0, if_pos hreg]
    rcases hcases with ⟨hq, hp, hM⟩ | ⟨hq, hp, hM, hak⟩
    · rw [hq, hg1] at hSV
      have hk0 : P.b * (μ P) / 2 * (σ.w - w1) ^ 2 = 0 := by
        have : 0 ≤ P.b * (μ P) / 2 * (σ.w - w1) ^ 2 := by positivity
        linarith
      have hw1' : σ.w = w1 := by
        have := sq_eq_zero_imp (σ.w - w1) (P.b * (μ P) / 2) (by positivity) hk0
        linarith
      obtain ⟨hR, -⟩ := outcome_low1 P hP c σ hQ hq hp hwa
      refine ⟨?_, ?_⟩
      · rw [hR, hw1', hw1]; field_simp; ring
      · rw [piS_def, hSV, hk0, sub_zero, hDA2S]
    · have hk : kf P σ.w = σ.w * (μ P) / P.α := rfl
      rw [hq, hg2 σ.w (kf P σ.w) hk] at hSV
      have hk0 : P.b / 2 * (kf P σ.w - wH) ^ 2 = 0 := by
        have : 0 ≤ P.b / 2 * (kf P σ.w - wH) ^ 2 := by positivity
        linarith
      have hkH : kf P σ.w = wH := by
        have := sq_eq_zero_imp (kf P σ.w - wH) (P.b / 2) (by positivity) hk0
        linarith
      obtain ⟨hR, -⟩ := outcome_low2 P hP c σ (kf P σ.w) hk hak hQ hq hp
      refine ⟨?_, ?_⟩
      · rw [hR, hkH, hwH, ← hR12]; field_simp; ring
      · rw [piS_def, hSV, hk0, sub_zero, hEq, hDA2S]
  · push Not at hreg
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
    obtain ⟨hR, -⟩ := outcome_high P hP c σ hQ hq hp hwa
    refine ⟨?_, ?_⟩
    · rw [hR, hwH', hwH, ← hR12]; field_simp; ring
    · rw [piS_def, hSV, hk0, sub_zero, hEq, hDA2S]
end DAH
namespace YieldPostpone.PrefBridge

open YieldPostpone

/-- The Interplay copy of the same parameter vector. -/
def toI (P : Preference.Params) : Interplay.Params := ⟨P.a, P.b, P.α, P.θ⟩

/-- Profiles of the two settings have identical fields. -/
def pfI (σ : Preference.Profile) : Interplay.Profile := ⟨σ.w, σ.Q, σ.q, σ.p, σ.pr⟩

def pfR (σ : Interplay.Profile) : Preference.Profile := ⟨σ.w, σ.Q, σ.q, σ.p, σ.pr⟩

lemma valid_iff (P : Preference.Params) : P.Valid ↔ (toI P).Valid := Iff.rfl

lemma mu_eq (P : Preference.Params) : Preference.μ P = Interplay.μ (toI P) := rfl

lemma spe_DA (P : Preference.Params) (c : ℝ) (σ : Preference.Profile) :
    Preference.IsSPE P c .DA σ ↔ Interplay.IsSPE (toI P) c .DA (pfI σ) := by
  constructor
  · rintro ⟨-, h2, h3, h4, h5, h6⟩
    exact ⟨fun w q hw hq => ⟨fun _ => h2 rfl w q hw hq, fun h => absurd h (by decide)⟩,
      h3, h4, h5, h6⟩
  · rintro ⟨h1, h3, h4, h5, h6⟩
    exact ⟨fun h => absurd h (by decide), fun _ w q hw hq => (h1 w q hw hq).1 rfl, h3, h4, h5, h6⟩

lemma spe_DR (P : Preference.Params) (c : ℝ) (σ : Preference.Profile) :
    Preference.IsSPE P c .DR σ ↔ Interplay.IsSPE (toI P) c .DR (pfI σ) := by
  constructor
  · rintro ⟨-, h2, h3, h4, h5, h6⟩
    exact ⟨fun w q hw hq => ⟨fun _ => h2 rfl w q hw hq, fun h => absurd h (by decide)⟩,
      h3, h4, h5, h6⟩
  · rintro ⟨h1, h3, h4, h5, h6⟩
    exact ⟨fun h => absurd h (by decide), fun _ w q hw hq => (h1 w q hw hq).1 rfl, h3, h4, h5, h6⟩

lemma spe_OR_to (P : Preference.Params) (c : ℝ) (σ : Preference.Profile) :
    Preference.IsSPE P c .OR σ → Interplay.IsSPE (toI P) c .OR (pfI σ) := by
  rintro ⟨h1, -, h3, h4, h5, h6⟩
  exact ⟨fun w q _ _ => ⟨fun h => absurd h (by decide), fun _ => h1 rfl w q⟩, h3, h4, h5, h6⟩

/-- Pay-by-order existence transfer: reset production to `Q = q` off the relevant subgames. -/
lemma spe_OR_of (P : Preference.Params) (c : ℝ) (σ : Interplay.Profile)
    (hσ : Interplay.IsSPE (toI P) c .OR σ) :
    Preference.IsSPE P c .OR ⟨σ.w, fun _ q => q, σ.q, σ.p, σ.pr⟩ := by
  obtain ⟨h1, h3, h4, h5, h6⟩ := hσ
  have hQ : ∀ w q, Interplay.wAdm (toI P) c .OR w → 0 ≤ q → σ.Q w q = q :=
    fun w q hw hq => (h1 w q hw hq).2 rfl
  have hRP : ∀ w q' p', Interplay.wAdm (toI P) c .OR w → 0 ≤ q' →
      Preference.retailerProfit P .OR ⟨σ.w, fun _ q => q, σ.q, σ.p, σ.pr⟩ w q' p' =
        Interplay.retailerProfit (toI P) .OR σ w q' p' := by
    intro w q' p' hw hq'
    simp only [Preference.retailerProfit, Interplay.retailerProfit, hQ w q' hw hq']
    rfl
  have hSV : ∀ w, Interplay.wAdm (toI P) c .OR w →
      Preference.supplierValue P c .OR ⟨σ.w, fun _ q => q, σ.q, σ.p, σ.pr⟩ w =
        Interplay.supplierValue (toI P) c .OR σ w := by
    intro w hw
    simp only [Preference.supplierValue, Interplay.supplierValue,
      hQ w (σ.q w) hw (h4 w hw).1]
    rfl
  refine ⟨fun _ _ _ => rfl, fun h => absurd h (by decide), h3, fun w hw => ?_, h5, ?_⟩
  · obtain ⟨a1, a2, a3⟩ := h4 w hw
    refine ⟨a1, a2, fun q' p' hq' hp' => ?_⟩
    rw [hRP w q' p' hw hq', hRP w (σ.q w) (σ.p w) hw a1]
    exact a3 q' p' hq' hp'
  · intro w' hw'
    show Preference.supplierValue P c .OR ⟨σ.w, fun _ q => q, σ.q, σ.p, σ.pr⟩ w' ≤
      Preference.supplierValue P c .OR ⟨σ.w, fun _ q => q, σ.q, σ.p, σ.pr⟩ σ.w
    rw [hSV w' hw', hSV σ.w h5]
    exact h6 w' hw'

end YieldPostpone.PrefBridge

open YieldPostpone YieldPostpone.Preference YieldPostpone.PrefBridge

lemma cDA_pos' (P : Params) (hP : P.Valid) : 0 < cDA P := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμ]; nlinarith
  have hs : Real.sqrt (μ P) ^ 2 = μ P := Real.sq_sqrt hμ0.le
  have hs0 : 0 ≤ Real.sqrt (μ P) := Real.sqrt_nonneg _
  have hθs : P.θ < Real.sqrt (μ P) := by
    rw [show P.θ = Real.sqrt (P.θ ^ 2) from (Real.sqrt_sq hθ0.le).symm]
    apply Real.sqrt_lt_sqrt (by positivity)
    rw [hμ]; nlinarith
  unfold cDA
  apply div_pos _ (by positivity)
  apply mul_pos (by positivity)
  nlinarith

lemma cDA_lt' (P : Params) (hP : P.Valid) : cDA P < P.a * μ P / P.b := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμ]; nlinarith
  have hs0 : 0 ≤ Real.sqrt (μ P) := Real.sqrt_nonneg _
  unfold cDA
  rw [div_lt_div_iff₀ (by positivity) hb]
  have h1 : P.α * (μ P - P.θ * Real.sqrt (μ P)) < μ P * (P.α + P.θ) := by
    have : 0 ≤ P.α * P.θ * Real.sqrt (μ P) := by positivity
    nlinarith
  have := mul_lt_mul_of_pos_left h1 (mul_pos ha hb)
  nlinarith

theorem solution (P : Params) (hP : P.Valid) :
    ∀ σ : Profile, IsSPE P (cDA P) .DA σ →
      piR P (cDA P) .DA σ = (P.b * cDA P - P.a * μ P) ^ 2 / (16 * P.b * μ P) ∧
      piS P (cDA P) .DA σ = (P.b * cDA P - P.a * μ P) ^ 2 / (8 * P.b * μ P) := by
  intro σ hσ
  exact YP3DA.boundary (toI P) hP (cDA P) (cDA_pos' P hP) (cDA_lt' P hP) rfl (pfI σ)
    ((spe_DA P (cDA P) σ).1 hσ)
