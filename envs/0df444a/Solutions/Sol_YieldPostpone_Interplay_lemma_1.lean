-- Prove2me | solution 1 for YieldPostpone.Interplay.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T05:00:28.455385+00:00
-- url     : https://prove2.me/submissions/f085eef9-5eb2-4e9c-8bb9-fbad153d3c1a

import Mathlib
import Definitions.Def_YieldPostpone_Interplay_Setting


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

namespace YP3L1i

/-- the cubic defining `θ₂(α)` -/
def pc (α x : ℝ) : ℝ :=
  -α ^ 3 + α ^ 2 * (5 + α) * x + (16 - 19 * α - 6 * α ^ 2) * x ^ 2 - 25 * (1 - α) * x ^ 3

lemma pc_cont (α : ℝ) : Continuous (pc α) := by unfold pc; fun_prop

lemma theta1_mul (α : ℝ) (hα1 : α < 1) :
    theta1 α * (8 * (1 - α)) = 1 - 4 * α + Real.sqrt (1 + 8 * α) := by
  unfold theta1
  have : (8 * (1 - α)) ≠ 0 := by
    have : 0 < 1 - α := by linarith
    positivity
  exact div_mul_cancel₀ _ this

lemma sqrt_facts (α : ℝ) (hα0 : 0 < α) :
    Real.sqrt (1 + 8 * α) ^ 2 = 1 + 8 * α ∧ 1 < Real.sqrt (1 + 8 * α) := by
  refine ⟨Real.sq_sqrt (by linarith), ?_⟩
  exact (Real.lt_sqrt (by norm_num)).mpr (by linarith)

/-- `p(θ₁) > 0` -/
lemma pc_theta1 (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) : 0 < pc α (theta1 α) := by
  obtain ⟨hr2, hr1⟩ := sqrt_facts α hα0
  set r := Real.sqrt (1 + 8 * α) with hr
  have ht := theta1_mul α hα1
  rw [← hr] at ht
  set t := theta1 α
  have h1α : 0 < 1 - α := by linarith
  set L := 8 * (1 - α) with hL
  have hL0 : 0 < L := by rw [hL]; positivity
  have e1 : pc α t * L ^ 3 = -α ^ 3 * L ^ 3 + α ^ 2 * (5 + α) * (t * L) * L ^ 2 +
      (16 - 19 * α - 6 * α ^ 2) * (t * L) ^ 2 * L - 25 * (1 - α) * (t * L) ^ 3 := by
    unfold pc; ring
  rw [ht] at e1
  have e2 : pc α t * L ^ 3 = 4 * (α - 1) *
      ((64*α^5 - 304*α^4 + 720*α^3 - 868*α^2 + 76*α - 39) +
        (16*α^4 - 32*α^3 - 60*α^2 + 232*α - 39) * r) := by
    rw [e1, hL]
    linear_combination (48*α^3 - 196*α^2 + 95*α + r*(25*α - 25) + 53) * hr2
  have hQ0 : 64*α^5 - 304*α^4 + 720*α^3 - 868*α^2 + 76*α - 39 < 0 := by
    have a1 : α ^ 5 ≤ α ^ 4 := pow_le_pow_of_le_one hα0.le hα1.le (by norm_num)
    have a2 : α ^ 3 ≤ α ^ 2 := pow_le_pow_of_le_one hα0.le hα1.le (by norm_num)
    have a3 : 0 ≤ α ^ 4 := by positivity
    nlinarith [sq_nonneg (α - 1 / 4)]
  have hN : (64*α^5 - 304*α^4 + 720*α^3 - 868*α^2 + 76*α - 39) ^ 2 -
      ((16*α^4 - 32*α^3 - 60*α^2 + 232*α - 39) * r) ^ 2 =
      4096 * α ^ 2 * ((3 - α) * (1 - α) ^ 3) * (α ^ 4 - 4 * α ^ 3 + 11 * α ^ 2 - 8 * α + 13) := by
    rw [mul_pow, hr2]; ring
  have hq4 : 0 < α ^ 4 - 4 * α ^ 3 + 11 * α ^ 2 - 8 * α + 13 := by
    nlinarith [sq_nonneg (α ^ 2 - 2 * α), sq_nonneg (α - 4 / 7)]
  have hNpos : 0 < 4096 * α ^ 2 * ((3 - α) * (1 - α) ^ 3) *
      (α ^ 4 - 4 * α ^ 3 + 11 * α ^ 2 - 8 * α + 13) := by
    have : 0 < 3 - α := by linarith
    positivity
  have hlt : (16*α^4 - 32*α^3 - 60*α^2 + 232*α - 39) * r <
      -(64*α^5 - 304*α^4 + 720*α^3 - 868*α^2 + 76*α - 39) := by
    have hsq : ((16*α^4 - 32*α^3 - 60*α^2 + 232*α - 39) * r) ^ 2 <
        (-(64*α^5 - 304*α^4 + 720*α^3 - 868*α^2 + 76*α - 39)) ^ 2 := by
      rw [neg_sq]; linarith
    exact lt_of_le_of_lt (le_abs_self _) (abs_lt_of_sq_lt_sq hsq (by linarith))
  have : 0 < pc α t * L ^ 3 := by
    rw [e2]
    have : (64*α^5 - 304*α^4 + 720*α^3 - 868*α^2 + 76*α - 39) +
        (16*α^4 - 32*α^3 - 60*α^2 + 232*α - 39) * r < 0 := by linarith
    nlinarith
  exact pos_of_mul_pos_left this (by positivity) |> fun h => by
    by_contra hc; push Not at hc
    have : pc α t * L ^ 3 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (by positivity)
    linarith

/-- the inflection point of `p` lies below `θ₁` -/
lemma infl (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    16 - 19 * α - 6 * α ^ 2 ≤ 75 * (1 - α) * theta1 α := by
  obtain ⟨hr2, hr1⟩ := sqrt_facts α hα0
  have ht := theta1_mul α hα1
  set r := Real.sqrt (1 + 8 * α) with hr
  have hX : 53 + 148 * α - 48 * α ^ 2 ≤ 75 * r := by
    have h0 : 0 ≤ 53 + 148 * α - 48 * α ^ 2 := by nlinarith
    have : (53 + 148 * α - 48 * α ^ 2) ^ 2 ≤ (75 * r) ^ 2 := by
      rw [mul_pow, hr2]; nlinarith [sq_nonneg α, mul_pos hα0 hα0]
    exact (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).mp this
  have : 75 * (1 - α) * theta1 α = 75 * (1 - 4 * α + r) / 8 := by
    rw [← ht]; ring
  rw [this]; nlinarith

lemma pc_neg_ge1 (α x : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hx : 1 ≤ x) : pc α x < 0 := by
  have e : pc α x = -(3 - α) ^ 2 + (α ^ 3 - 7 * α ^ 2 + 37 * α - 43) * (x - 1) +
      (-59 + 56 * α - 6 * α ^ 2) * (x - 1) ^ 2 - 25 * (1 - α) * (x - 1) ^ 3 := by
    unfold pc; ring
  rw [e]
  have ht : 0 ≤ x - 1 := by linarith
  have c1 : α ^ 3 - 7 * α ^ 2 + 37 * α - 43 < 0 := by nlinarith [pow_pos hα0 3]
  have c2 : -59 + 56 * α - 6 * α ^ 2 < 0 := by nlinarith
  have h1 : (α ^ 3 - 7 * α ^ 2 + 37 * α - 43) * (x - 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg c1.le ht
  have h2 : (-59 + 56 * α - 6 * α ^ 2) * (x - 1) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg c2.le (by positivity)
  have h3 : 0 ≤ 25 * (1 - α) * (x - 1) ^ 3 := by
    have : 0 < 1 - α := by linarith
    positivity
  have h4 : 0 < (3 - α) ^ 2 := by
    have : 0 < 3 - α := by linarith
    positivity
  linarith

lemma theta1_lt_one (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) : theta1 α < 1 := by
  obtain ⟨hr2, hr1⟩ := sqrt_facts α hα0
  have ht := theta1_mul α hα1
  have h1α : 0 < 1 - α := by linarith
  have hr7 : Real.sqrt (1 + 8 * α) < 7 - 4 * α := by
    rw [show 7 - 4 * α = Real.sqrt ((7 - 4 * α) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_lt_sqrt (by linarith) (by nlinarith)
  by_contra h; push Not at h
  have := mul_le_mul_of_nonneg_right h (by positivity : (0:ℝ) ≤ 8 * (1 - α))
  linarith

lemma theta1_pos (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) : 0 < theta1 α := by
  obtain ⟨hr2, hr1⟩ := sqrt_facts α hα0
  unfold theta1
  apply div_pos _ (by linarith)
  -- `√(1+8α) > 4α - 1`
  rcases le_or_gt (4 * α - 1) 0 with h | h
  · linarith
  · have : 4 * α - 1 < Real.sqrt (1 + 8 * α) := by
      rw [show 4 * α - 1 = Real.sqrt ((4 * α - 1) ^ 2) by rw [Real.sqrt_sq h.le]]
      exact Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
    linarith

/-- the properties of `θ₂` -/
lemma theta2_props (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    pc α (theta2 α) = 0 ∧ theta1 α < theta2 α ∧ ∀ x, theta2 α < x → pc α x < 0 := by
  have hset : theta2 α = sSup {x : ℝ | pc α x = 0} := rfl
  have hcl : IsClosed {x : ℝ | pc α x = 0} := isClosed_eq (pc_cont α) continuous_const
  have hbdd : BddAbove {x : ℝ | pc α x = 0} := by
    refine ⟨1, fun x hx => ?_⟩
    by_contra h; push Not at h
    have := pc_neg_ge1 α x hα0 hα1 h.le
    exact absurd hx (by simp only [Set.mem_setOf_eq]; linarith)
  have h1 := pc_theta1 α hα0 hα1
  have h1l := theta1_lt_one α hα0 hα1
  have hpc1 : pc α 1 < 0 := pc_neg_ge1 α 1 hα0 hα1 le_rfl
  obtain ⟨ρ, hρ, hρ0⟩ : ∃ ρ ∈ Set.Icc (theta1 α) 1, pc α ρ = 0 := by
    have := intermediate_value_Icc' h1l.le (pc_cont α).continuousOn
    exact this ⟨hpc1.le, h1.le⟩
  have hne : ({x : ℝ | pc α x = 0}).Nonempty := ⟨ρ, hρ0⟩
  have hmem := hcl.csSup_mem hne hbdd
  rw [← hset] at hmem
  have hρθ : theta1 α < ρ := by
    rcases hρ.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hρ0; linarith
  have hρle : ρ ≤ theta2 α := by rw [hset]; exact le_csSup hbdd hρ0
  refine ⟨hmem, lt_of_lt_of_le hρθ hρle, fun x hx => ?_⟩
  by_contra hc; push Not at hc
  rcases le_or_gt 1 x with hx1 | hx1
  · have := pc_neg_ge1 α x hα0 hα1 hx1; linarith
  · obtain ⟨y, hy, hy0⟩ : ∃ y ∈ Set.Icc x 1, pc α y = 0 := by
      have := intermediate_value_Icc' hx1.le (pc_cont α).continuousOn
      exact this ⟨hpc1.le, hc⟩
    have : y ≤ theta2 α := by rw [hset]; exact le_csSup hbdd hy0
    linarith [hy.1]

/-- `p > 0` strictly between `θ₁` and `θ₂` -/
lemma pc_pos_between (α x : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (h1 : theta1 α < x)
    (h2 : x < theta2 α) : 0 < pc α x := by
  obtain ⟨hz, h12, -⟩ := theta2_props α hα0 hα1
  have hp1 := pc_theta1 α hα0 hα1
  have hin := infl α hα0 hα1
  set t1 := theta1 α
  set t2 := theta2 α
  have key : pc α x * (t2 - t1) = pc α t1 * (t2 - x) + pc α t2 * (x - t1) +
      (t2 - t1) * (x - t1) * (x - t2) *
        (-25 * (1 - α) * (x + t1 + t2) + (16 - 19 * α - 6 * α ^ 2)) := by
    unfold pc; ring
  rw [hz, zero_mul, add_zero] at key
  have hlin : -25 * (1 - α) * (x + t1 + t2) + (16 - 19 * α - 6 * α ^ 2) ≤ 0 := by
    have : 3 * t1 < x + t1 + t2 := by linarith
    have h1α : 0 < 1 - α := by linarith
    nlinarith
  have hprod : (t2 - t1) * (x - t1) * (x - t2) < 0 := by
    have : 0 < (t2 - t1) * (x - t1) := mul_pos (by linarith) (by linarith)
    exact mul_neg_of_pos_of_neg this (by linarith)
  have : 0 < pc α x * (t2 - t1) := by
    rw [key]
    have : 0 ≤ (t2 - t1) * (x - t1) * (x - t2) *
        (-25 * (1 - α) * (x + t1 + t2) + (16 - 19 * α - 6 * α ^ 2)) :=
      mul_nonneg_of_nonpos_of_nonpos hprod.le hlin
    have : 0 < pc α t1 * (t2 - x) := mul_pos hp1 (by linarith)
    linarith
  by_contra hc; push Not at hc
  have : pc α x * (t2 - t1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (by linarith)
  linarith

end YP3L1i


open YieldPostpone.Interplay

namespace YP3L1i

noncomputable def Kq (P : Params) : ℝ := 4 * P.b * μ P * (P.a * P.α - P.b * what P)
noncomputable def Aq (P : Params) : ℝ := P.α ^ 2 * P.b ^ 2
noncomputable def Bq (P : Params) : ℝ := -2 * P.α ^ 2 * P.a * P.b * μ P + Kq P
noncomputable def Cq (P : Params) : ℝ := P.α ^ 2 * P.a ^ 2 * μ P ^ 2 - Kq P * what P

lemma cOA2_eq (P : Params) :
    cOA2 P = (-Bq P + Real.sqrt (Bq P ^ 2 - 4 * Aq P * Cq P)) / (2 * Aq P) := rfl

lemma qr1 (A B C c : ℝ) (hA : 0 < A) (h : A * c ^ 2 + B * c + C < 0) :
    c < (-B + Real.sqrt (B ^ 2 - 4 * A * C)) / (2 * A) := by
  have hD : (2 * A * c + B) ^ 2 < B ^ 2 - 4 * A * C := by nlinarith
  have h1 : 2 * A * c + B < Real.sqrt (B ^ 2 - 4 * A * C) := by
    calc 2 * A * c + B ≤ |2 * A * c + B| := le_abs_self _
      _ = Real.sqrt ((2 * A * c + B) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ < Real.sqrt (B ^ 2 - 4 * A * C) := Real.sqrt_lt_sqrt (sq_nonneg _) hD
  rw [lt_div_iff₀ (by positivity)]; linarith

lemma qr2 (A B C : ℝ) (hA : 0 < A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    (-B + Real.sqrt (B ^ 2 - 4 * A * C)) / (2 * A) ≤ 0 := by
  have : Real.sqrt (B ^ 2 - 4 * A * C) ≤ B := by
    calc Real.sqrt (B ^ 2 - 4 * A * C) ≤ Real.sqrt (B ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = B := Real.sqrt_sq hB
  apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

lemma qr3 (A B C : ℝ) (hA : 0 < A) (hC : C < 0) :
    0 < (-B + Real.sqrt (B ^ 2 - 4 * A * C)) / (2 * A) := by
  have : B < Real.sqrt (B ^ 2 - 4 * A * C) := by
    calc B ≤ |B| := le_abs_self _
      _ = Real.sqrt (B ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ < Real.sqrt (B ^ 2 - 4 * A * C) := Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
  apply div_pos (by linarith) (by positivity)

/-- the algebra of the OA thresholds, with `s = √μ` -/
lemma oa_alg (P : Params) (hP : P.Valid) :
    Aq P * cOA1 P ^ 2 + Bq P * cOA1 P + Cq P < 0 ∧
    Cq P * (P.α + P.θ) ^ 2 = P.a ^ 2 * P.α ^ 2 * μ P * Real.sqrt (μ P) *
      (Real.sqrt (μ P) * ((P.α - P.θ) ^ 2 + 4 * P.θ ^ 2) -
        4 * P.θ * (P.α + P.θ - 2 * P.α * P.θ)) ∧
    cOA1 P * (P.b * (P.α + P.θ)) =
      P.a * P.α * (μ P - P.α * P.θ - 2 * P.θ * Real.sqrt (μ P)) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  set s := Real.sqrt (μ P) with hsdef
  have hs : s ^ 2 = μ P := Real.sq_sqrt hμ0.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hμ0
  have hαs : P.α < s := by
    rw [hsdef]; apply Real.lt_sqrt_of_sq_lt; rw [hμ]; nlinarith [mul_pos hα0 h1θ]
  have hαθ : 0 < P.α + P.θ := by linarith
  have hW : P.b * what P * (P.α + P.θ) = P.a * P.α * (μ P - P.θ * s) := by
    unfold what; rw [← hsdef]; field_simp
  have hc1 : cOA1 P * (P.b * (P.α + P.θ)) =
      P.a * P.α * (μ P - P.α * P.θ - 2 * P.θ * s) := by
    unfold cOA1; rw [← hsdef]; field_simp
  have hbc1 : P.b * cOA1 P = 2 * (P.b * what P) - P.a * P.α := by
    have : (P.b * cOA1 P) * (P.α + P.θ) = (2 * (P.b * what P) - P.a * P.α) * (P.α + P.θ) := by
      have e : (2 * (P.b * what P) - P.a * P.α) * (P.α + P.θ) =
          2 * (P.b * what P * (P.α + P.θ)) - P.a * P.α * (P.α + P.θ) := by ring
      rw [e, hW]
      have e2 : P.b * cOA1 P * (P.α + P.θ) = cOA1 P * (P.b * (P.α + P.θ)) := by ring
      rw [e2, hc1, hμ]; ring
    exact mul_right_cancel₀ hαθ.ne' this
  set W := P.b * what P with hWdef
  have E1 : (P.a * μ P + P.a * P.α - 2 * W) * (P.α + P.θ) = P.a * P.θ * (s + P.α) ^ 2 := by
    have e : (P.a * μ P + P.a * P.α - 2 * W) * (P.α + P.θ) =
        P.a * μ P * (P.α + P.θ) + P.a * P.α * (P.α + P.θ) - 2 * (W * (P.α + P.θ)) := by ring
    rw [e, hW]
    linear_combination (-(P.a * P.θ)) * hs - (P.a * P.α) * hμ
  have E2 : (P.a * P.α - W) * (P.α + P.θ) = P.a * P.α * P.θ * (P.α + s) := by
    have e : (P.a * P.α - W) * (P.α + P.θ) = P.a * P.α * (P.α + P.θ) - W * (P.α + P.θ) := by ring
    rw [e, hW, hμ]; ring
  have hK : Kq P = 4 * μ P * (P.a * P.α - W) * P.b := by unfold Kq; rw [hWdef]; ring
  refine ⟨?_, ?_, hc1⟩
  · have hh : Aq P * cOA1 P ^ 2 + Bq P * cOA1 P + Cq P =
        P.α ^ 2 * (P.a * μ P - P.b * cOA1 P) ^ 2 - 4 * μ P * (P.a * P.α - W) * (W - P.b * cOA1 P) := by
      unfold Aq Bq Cq; rw [hK, hWdef]; ring
    rw [hh, hbc1]
    have e3 : W - (2 * W - P.a * P.α) = P.a * P.α - W := by ring
    have e4 : P.a * μ P - (2 * W - P.a * P.α) = P.a * μ P + P.a * P.α - 2 * W := by ring
    rw [e3, e4]
    have hpos : 0 < (P.α + P.θ) ^ 2 := by positivity
    have key : (P.α ^ 2 * (P.a * μ P + P.a * P.α - 2 * W) ^ 2 - 4 * μ P * (P.a * P.α - W) * (P.a * P.α - W)) *
        (P.α + P.θ) ^ 2 = P.a ^ 2 * P.α ^ 2 * P.θ ^ 2 * (s + P.α) ^ 2 * ((P.α - s) * (P.α + 3 * s)) := by
      have : (P.α ^ 2 * (P.a * μ P + P.a * P.α - 2 * W) ^ 2 - 4 * μ P * (P.a * P.α - W) * (P.a * P.α - W)) *
          (P.α + P.θ) ^ 2 = P.α ^ 2 * ((P.a * μ P + P.a * P.α - 2 * W) * (P.α + P.θ)) ^ 2 -
            4 * μ P * ((P.a * P.α - W) * (P.α + P.θ)) ^ 2 := by ring
      rw [this, E1, E2, ← hs]; ring
    have hneg : P.a ^ 2 * P.α ^ 2 * P.θ ^ 2 * (s + P.α) ^ 2 * ((P.α - s) * (P.α + 3 * s)) < 0 := by
      apply mul_neg_of_pos_of_neg (by positivity)
      exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
    by_contra hc; push Not at hc
    have := mul_nonneg hc hpos.le
    linarith
  · have hC : Cq P = P.α ^ 2 * P.a ^ 2 * μ P ^ 2 - 4 * μ P * (P.a * P.α - W) * W := by
      unfold Cq; rw [hK, hWdef]; ring
    rw [hC]
    have : (P.α ^ 2 * P.a ^ 2 * μ P ^ 2 - 4 * μ P * (P.a * P.α - W) * W) * (P.α + P.θ) ^ 2 =
        P.α ^ 2 * P.a ^ 2 * μ P ^ 2 * (P.α + P.θ) ^ 2 -
          4 * μ P * ((P.a * P.α - W) * (P.α + P.θ)) * (W * (P.α + P.θ)) := by ring
    rw [this, E2, hW, ← hs]
    have hs' : s ^ 2 = P.α * (1 - P.θ) + P.θ := by rw [hs, hμ]
    linear_combination (-4 * P.a ^ 2 * P.α ^ 2 * s ^ 3 * P.θ) * hs'

end YP3L1i


open YieldPostpone.Interplay

namespace YP3OA
open YP3DA

/-- the retailer's OA objective in the DA-low form, at effective price `w'` -/
def RN (P : Params) (w' q p : ℝ) : ℝ :=
  P.θ * (p * min (P.a - P.b * p) q - w' * q) +
    (1 - P.θ) * (p * min (P.a - P.b * p) (P.α * q) - w' * (P.α * q))

lemma wAdm_OA (P : Params) (c w : ℝ) : wAdm P c .OA w ↔ c < w ∧ w < P.a / P.b := by
  simp [wAdm, Scenario.byDelivery]

lemma spe_Q (P : Params) (c : ℝ) (σ : Profile) (hσ : IsSPE P c .OA σ) (w q : ℝ)
    (hw : wAdm P c .OA w) (hq : 0 ≤ q) : σ.Q w q = q :=
  (hσ.1 w q hw hq).2 rfl

lemma rp_OA (P : Params) (hP : P.Valid) (σ : Profile) (w q p : ℝ) (hQ : σ.Q w q = q)
    (hq : 0 ≤ q) :
    retailerProfit P .OA σ w q p = RN P (w / μ P) q p := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by
    rw [hμ]; have : 0 < 1 - P.θ := by linarith
    positivity
  unfold retailerProfit E RN
  simp only [delivered, hQ, Scenario.responsive, Scenario.byDelivery, transfer, salesRev, demand,
    Bool.false_eq_true, if_false]
  have h1 : min (1 * q) q = q := by simp
  have h2 : min (P.α * q) q = P.α * q := min_eq_left (by nlinarith)
  rw [h1, h2]
  field_simp
  rw [hμ]; ring

lemma sv_OA (P : Params) (c : ℝ) (σ : Profile) (w : ℝ) (hQ : σ.Q w (σ.q w) = σ.q w) :
    supplierValue P c .OA σ w = (w - c) * σ.q w := by
  unfold supplierValue supplierProfit E transfer
  rw [hQ]
  simp [Scenario.byDelivery]
  ring

/-- above `aμ/b` the retailer's objective is negative for every positive order -/
lemma RN_neg (P : Params) (hP : P.Valid) (w q p : ℝ) (hw : P.a * μ P ≤ P.b * w) (hq : 0 < q)
    (hp : pAdm P p) : RN P (w / μ P) q p < 0 := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  obtain ⟨hp0, hpa⟩ := (pAdm_iff P hb p).mp hp
  have m1 : p * min (P.a - P.b * p) q ≤ p * q := mul_le_mul_of_nonneg_left (min_le_right _ _) hp0.le
  have m2 : p * min (P.a - P.b * p) (P.α * q) ≤ p * (P.α * q) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) hp0.le
  have e : RN P (w / μ P) q p ≤ (p * μ P - w) * q := by
    have this : w / μ P * q * (P.θ + (1 - P.θ) * P.α) = w * q := by
      rw [show P.θ + (1 - P.θ) * P.α = μ P by rw [hμ]; ring]; field_simp
    have e2 : RN P (w / μ P) q p = P.θ * (p * min (P.a - P.b * p) q) +
        (1 - P.θ) * (p * min (P.a - P.b * p) (P.α * q)) - w / μ P * q * (P.θ + (1 - P.θ) * P.α) := by
      unfold RN; ring
    have k1 := mul_le_mul_of_nonneg_left m1 hθ0.le
    have k2 := mul_le_mul_of_nonneg_left m2 h1θ.le
    rw [e2, this, hμ]
    linarith
  have : p * μ P < w := by
    have h1 : P.b * (p * μ P) < P.a * μ P := by nlinarith
    nlinarith
  nlinarith

/-- the retailer's two candidates and the switching price `ŵ`:
`(a - b w/α) - √μ (a - b w/μ) = b(√μ - α)(ŵ - w)/(α √μ)` -/
lemma switch_id (P : Params) (hP : P.Valid) (w : ℝ) :
    (P.a - P.b * (w / μ P * μ P / P.α)) - Real.sqrt (μ P) * (P.a - P.b * (w / μ P)) =
      P.b * (Real.sqrt (μ P) - P.α) * (what P - w) / (P.α * Real.sqrt (μ P)) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  have hs0 : 0 < Real.sqrt (μ P) := Real.sqrt_pos.mpr hμ0
  have hs : Real.sqrt (μ P) ^ 2 = μ P := Real.sq_sqrt hμ0.le
  have hX := cDA_eq P hP
  have hw : what P = cDA P := rfl
  rw [hw]
  set s := Real.sqrt (μ P)
  have e1 : w / μ P * μ P / P.α = w / P.α := by field_simp
  rw [e1, ← hs]
  have hne : P.α * s ≠ 0 := by positivity
  rw [eq_div_iff hne]
  have : (P.a - P.b * (w / P.α) - s * (P.a - P.b * (w / s ^ 2))) * (P.α * s) =
      P.a * P.α * s - P.a * P.α * s ^ 2 - P.b * w * s + P.b * w * P.α := by
    field_simp; ring
  rw [this]
  linear_combination (-1 : ℝ) * hX

end YP3OA


open YieldPostpone.Interplay

namespace YP3OA
open YP3DA

/-- the retailer's optimal value in OA at `w` (when `b w < a μ`) -/
noncomputable def Mo (P : Params) (w : ℝ) : ℝ :=
  if Real.sqrt (μ P) * (P.a - P.b * (w / μ P)) < P.a - P.b * (w / μ P * μ P / P.α) then
    (P.a - P.b * (w / μ P * μ P / P.α)) ^ 2 / (4 * P.b)
  else μ P * (P.a - P.b * (w / μ P)) ^ 2 / (4 * P.b)

lemma RN_le (P : Params) (hP : P.Valid) (w q p : ℝ) (hw0 : 0 < w) (hwa : P.b * w < P.a * μ P)
    (hq : 0 ≤ q) (hp : pAdm P p) :
    RN P (w / μ P) q p ≤ Mo P w ∧
    (RN P (w / μ P) q p = Mo P w →
      (q = (P.a - P.b * (w / μ P)) / 2 ∧ p = (P.a + P.b * (w / μ P)) / (2 * P.b) ∧
        Mo P w = μ P * (P.a - P.b * (w / μ P)) ^ 2 / (4 * P.b)) ∨
      (q = (P.a - P.b * (w / μ P * μ P / P.α)) / (2 * P.α) ∧
        p = (P.a + P.b * (w / μ P * μ P / P.α)) / (2 * P.b) ∧
        Mo P w = (P.a - P.b * (w / μ P * μ P / P.α)) ^ 2 / (4 * P.b) ∧
        0 < P.a - P.b * (w / μ P * μ P / P.α))) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  obtain ⟨hp0, hpa⟩ := (pAdm_iff P hb p).mp hp
  have hw' : P.b * (w / μ P) < P.a := by
    rw [mul_div_assoc', div_lt_iff₀ hμ0]; linarith
  exact RL_le P.a P.b P.α P.θ (μ P) (Real.sqrt (μ P)) (w / μ P) q p _ (Mo P w) hb hα0 hα1 hθ0 hθ1
    hμ (Real.sqrt_pos.mpr hμ0) (Real.sq_sqrt hμ0.le) (div_pos hw0 hμ0) hw' hq hp0 hpa rfl rfl

/-- the candidates attain `Mo` -/
lemma Mo_attained (P : Params) (hP : P.Valid) (w : ℝ) (hw0 : 0 < w) (hwa : P.b * w < P.a * μ P) :
    (Real.sqrt (μ P) * (P.a - P.b * (w / μ P)) < P.a - P.b * (w / μ P * μ P / P.α) →
      pAdm P ((P.a + P.b * (w / μ P * μ P / P.α)) / (2 * P.b)) ∧
      0 ≤ (P.a - P.b * (w / μ P * μ P / P.α)) / (2 * P.α) ∧
      RN P (w / μ P) ((P.a - P.b * (w / μ P * μ P / P.α)) / (2 * P.α))
        ((P.a + P.b * (w / μ P * μ P / P.α)) / (2 * P.b)) = Mo P w) ∧
    (¬ Real.sqrt (μ P) * (P.a - P.b * (w / μ P)) < P.a - P.b * (w / μ P * μ P / P.α) →
      pAdm P ((P.a + P.b * (w / μ P)) / (2 * P.b)) ∧
      0 ≤ (P.a - P.b * (w / μ P)) / 2 ∧
      RN P (w / μ P) ((P.a - P.b * (w / μ P)) / 2) ((P.a + P.b * (w / μ P)) / (2 * P.b)) = Mo P w) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  have hs0 : 0 < Real.sqrt (μ P) := Real.sqrt_pos.mpr hμ0
  have hw' : P.b * (w / μ P) < P.a := by
    rw [mul_div_assoc', div_lt_iff₀ hμ0]; linarith
  have hw'0 : 0 < w / μ P := div_pos hw0 hμ0
  refine ⟨fun hC => ?_, fun hC => ?_⟩
  · have hak : 0 < P.a - P.b * (w / μ P * μ P / P.α) := by
      have : 0 < Real.sqrt (μ P) * (P.a - P.b * (w / μ P)) := mul_pos hs0 (by linarith)
      linarith
    have hk0 : 0 < w / μ P * μ P / P.α := by positivity
    refine ⟨?_, by positivity, ?_⟩
    · rw [pAdm_iff P hb]
      refine ⟨by positivity, ?_⟩
      have : P.b * ((P.a + P.b * (w / μ P * μ P / P.α)) / (2 * P.b)) =
          (P.a + P.b * (w / μ P * μ P / P.α)) / 2 := by field_simp
      rw [this]; linarith
    · unfold RN Mo; rw [if_pos hC]
      exact cand2_val P.a P.b P.α P.θ (μ P) (w / μ P) _ hb hα0 hα1 hμ rfl hak
  · refine ⟨?_, by linarith, ?_⟩
    · rw [pAdm_iff P hb]
      refine ⟨by positivity, ?_⟩
      have : P.b * ((P.a + P.b * (w / μ P)) / (2 * P.b)) = (P.a + P.b * (w / μ P)) / 2 := by
        field_simp
      rw [this]; linarith
    · unfold RN Mo; rw [if_neg hC]
      exact cand1_val P.a P.b P.α P.θ (μ P) (w / μ P) hb hα0 hα1 hμ hw'

/-- the switch between the two candidates happens at `ŵ` -/
lemma switch_sign (P : Params) (hP : P.Valid) (w : ℝ) :
    (w < what P → Real.sqrt (μ P) * (P.a - P.b * (w / μ P)) < P.a - P.b * (w / μ P * μ P / P.α)) ∧
    (what P < w → P.a - P.b * (w / μ P * μ P / P.α) < Real.sqrt (μ P) * (P.a - P.b * (w / μ P))) ∧
    (w = what P → P.a - P.b * (w / μ P * μ P / P.α) = Real.sqrt (μ P) * (P.a - P.b * (w / μ P))) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  have hs0 : 0 < Real.sqrt (μ P) := Real.sqrt_pos.mpr hμ0
  have hαs : P.α < Real.sqrt (μ P) := by
    apply Real.lt_sqrt_of_sq_lt; rw [hμ]; nlinarith [mul_pos hα0 h1θ]
  have e := switch_id P hP w
  have hk : 0 < P.b * (Real.sqrt (μ P) - P.α) / (P.α * Real.sqrt (μ P)) := by
    apply div_pos (mul_pos hb (by linarith)) (by positivity)
  have e' : P.a - P.b * (w / μ P * μ P / P.α) - Real.sqrt (μ P) * (P.a - P.b * (w / μ P)) =
      P.b * (Real.sqrt (μ P) - P.α) / (P.α * Real.sqrt (μ P)) * (what P - w) := by
    rw [e]; ring
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := mul_pos hk (sub_pos.2 h); linarith
  · have := mul_neg_of_pos_of_neg hk (sub_neg.2 h); linarith
  · subst h; rw [sub_self, mul_zero] at e'; linarith

/-- The retailer's response in any SPE of OA, for `c < w < aμ/b`. -/
lemma resp_OA (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (hσ : IsSPE P c .OA σ) (w : ℝ) (hw : wAdm P c .OA w) (hwa : P.b * w < P.a * μ P) :
    (σ.q w = (P.a - P.b * (w / μ P)) / 2 ∧ σ.p w = (P.a + P.b * (w / μ P)) / (2 * P.b) ∧
        what P ≤ w) ∨
    (σ.q w = (P.a - P.b * (w / μ P * μ P / P.α)) / (2 * P.α) ∧
        σ.p w = (P.a + P.b * (w / μ P * μ P / P.α)) / (2 * P.b) ∧ w ≤ what P ∧
        0 < P.a - P.b * (w / μ P * μ P / P.α)) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  have hs0 : 0 < Real.sqrt (μ P) := Real.sqrt_pos.mpr hμ0
  have hs : Real.sqrt (μ P) ^ 2 = μ P := Real.sq_sqrt hμ0.le
  obtain ⟨hw1, hw2⟩ := (wAdm_OA P c w).mp hw
  have hw0 : 0 < w := by linarith
  obtain ⟨hq0, hpA, hopt⟩ := hσ.2.2.1 w hw
  have hpA' := hpA rfl
  have hQ : ∀ q, 0 ≤ q → σ.Q w q = q := fun q hq => spe_Q P c σ hσ w q hw hq
  have hR : ∀ q p, 0 ≤ q → retailerProfit P .OA σ w q p = RN P (w / μ P) q p :=
    fun q p hq => rp_OA P hP σ w q p (hQ q hq) hq
  obtain ⟨hle, heq⟩ := RN_le P hP w (σ.q w) (σ.p w) hw0 hwa hq0 hpA'
  have hge : Mo P w ≤ RN P (w / μ P) (σ.q w) (σ.p w) := by
    obtain ⟨A1, A2⟩ := Mo_attained P hP w hw0 hwa
    by_cases hC : Real.sqrt (μ P) * (P.a - P.b * (w / μ P)) < P.a - P.b * (w / μ P * μ P / P.α)
    · obtain ⟨hpa, hqa, hv⟩ := A1 hC
      have := hopt _ _ hqa (fun _ => hpa)
      rw [hR _ _ hqa, hR _ _ hq0, hv] at this; exact this
    · obtain ⟨hpa, hqa, hv⟩ := A2 hC
      have := hopt _ _ hqa (fun _ => hpa)
      rw [hR _ _ hqa, hR _ _ hq0, hv] at this; exact this
  have hcases := heq (le_antisymm hle hge)
  obtain ⟨sw1, sw2, -⟩ := switch_sign P hP w
  have hw'a : 0 < P.a - P.b * (w / μ P) := by
    have : P.b * (w / μ P) < P.a := by rw [mul_div_assoc', div_lt_iff₀ hμ0]; linarith
    linarith
  rcases hcases with ⟨h1, h2, hM⟩ | ⟨h1, h2, hM, hak⟩
  · refine Or.inl ⟨h1, h2, ?_⟩
    by_contra hlt; push Not at hlt
    have hC := sw1 hlt
    unfold Mo at hM; rw [if_pos hC] at hM
    have hpos : 0 < Real.sqrt (μ P) * (P.a - P.b * (w / μ P)) := mul_pos hs0 hw'a
    have : (Real.sqrt (μ P) * (P.a - P.b * (w / μ P))) ^ 2 <
        (P.a - P.b * (w / μ P * μ P / P.α)) ^ 2 := pow_lt_pow_left₀ hC hpos.le (by norm_num)
    rw [mul_pow, hs] at this
    have hne : (P.a - P.b * (w / μ P * μ P / P.α)) ^ 2 / (4 * P.b) ≠
        μ P * (P.a - P.b * (w / μ P)) ^ 2 / (4 * P.b) := by
      intro h; have := (div_left_inj' (by positivity : (4 * P.b) ≠ 0)).mp h; linarith
    exact hne hM
  · refine Or.inr ⟨h1, h2, ?_, hak⟩
    by_contra hlt; push Not at hlt
    have hC := sw2 hlt
    unfold Mo at hM; rw [if_neg (not_lt.mpr hC.le)] at hM
    have : (P.a - P.b * (w / μ P * μ P / P.α)) ^ 2 <
        (Real.sqrt (μ P) * (P.a - P.b * (w / μ P))) ^ 2 := pow_lt_pow_left₀ hC hak.le (by norm_num)
    rw [mul_pow, hs] at this
    have hne : μ P * (P.a - P.b * (w / μ P)) ^ 2 / (4 * P.b) ≠
        (P.a - P.b * (w / μ P * μ P / P.α)) ^ 2 / (4 * P.b) := by
      intro h; have := (div_left_inj' (by positivity : (4 * P.b) ≠ 0)).mp h; linarith
    exact hne hM

/-- the retailer orders nothing at `w ≥ aμ/b` -/
lemma resp_zero (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (hσ : IsSPE P c .OA σ) (w : ℝ) (hw : wAdm P c .OA w) (hwa : P.a * μ P ≤ P.b * w) :
    σ.q w = 0 := by
  obtain ⟨hq0, hpA, hopt⟩ := hσ.2.2.1 w hw
  have hpA' := hpA rfl
  have hQ : ∀ q, 0 ≤ q → σ.Q w q = q := fun q hq => spe_Q P c σ hσ w q hw hq
  have h0 := hopt 0 (σ.p w) le_rfl (fun _ => hpA')
  rw [rp_OA P hP σ w _ _ (hQ 0 le_rfl) le_rfl, rp_OA P hP σ w _ _ (hQ _ hq0) hq0] at h0
  have hz : RN P (w / μ P) 0 (σ.p w) = 0 := by
    have hP' := hP
    obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
    obtain ⟨hp0, hpa⟩ := (pAdm_iff P hb _).mp hpA'
    have hm : min (P.a - P.b * σ.p w) 0 = 0 := min_eq_right (by linarith)
    unfold RN
    simp only [mul_zero, hm]
    ring
  rw [hz] at h0
  by_contra hne
  have := RN_neg P hP w (σ.q w) (σ.p w) hwa (lt_of_le_of_ne hq0 (Ne.symm hne)) hpA'
  linarith

end YP3OA


open YieldPostpone.Interplay

namespace YP3OA
open YP3DA YP3L1i

lemma k_eq (P : Params) (hP : P.Valid) (w : ℝ) : w / μ P * μ P / P.α = w / P.α := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ0 : 0 < μ P := by
    have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
    rw [hμ]; have : 0 < 1 - P.θ := by linarith
    positivity
  field_simp

/-- supplier's value on the inflated branch -/
noncomputable def g1 (P : Params) (c w : ℝ) : ℝ := (w - c) * ((P.a - P.b * (w / P.α)) / (2 * P.α))
/-- supplier's value on the non-inflated branch -/
noncomputable def g2 (P : Params) (c w : ℝ) : ℝ := (w - c) * ((P.a - P.b * (w / μ P)) / 2)

lemma g1_form (P : Params) (hP : P.Valid) (c w : ℝ) :
    g1 P c w = (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) -
      P.b / (2 * P.α ^ 2) * (w - (P.a * P.α + P.b * c) / (2 * P.b)) ^ 2 := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  unfold g1; field_simp; ring

lemma g2_form (P : Params) (hP : P.Valid) (c w : ℝ) :
    g2 P c w = (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * μ P) -
      P.b / (2 * μ P) * (w - (P.a * μ P + P.b * c) / (2 * P.b)) ^ 2 := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hμ0 : 0 < μ P := by
    have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
    rw [hμ]; have : 0 < 1 - P.θ := by linarith
    positivity
  unfold g2; field_simp; ring

lemma h_eq (P : Params) (hP : P.Valid) (c : ℝ) :
    Aq P * c ^ 2 + Bq P * c + Cq P =
      8 * P.b * μ P * P.α ^ 2 * ((P.a * μ P - P.b * c) ^ 2 / (8 * P.b * μ P) - g1 P c (what P)) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hμ0 : 0 < μ P := by
    have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
    rw [hμ]; have : 0 < 1 - P.θ := by linarith
    positivity
  unfold Aq Bq Cq Kq g1; field_simp; ring

/-- scalar facts on `ŵ`, `c^OA_1`, and the quadratic `h` -/
lemma oa_facts (P : Params) (hP : P.Valid) :
    0 < what P ∧ P.b * what P < P.a * P.α ∧
    P.b * cOA1 P = 2 * (P.b * what P) - P.a * P.α ∧
    (∀ c, c < what P → P.b * c < P.a * P.α →
      (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * μ P) < (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2)) ∧
    (∀ c, c < what P → g2 P c (what P) < g1 P c (what P)) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  set s := Real.sqrt (μ P) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hμ0
  have hs : s ^ 2 = μ P := Real.sq_sqrt hμ0.le
  have hX := cDA_eq P hP
  have hw : what P = cDA P := rfl
  obtain ⟨hαs2, hs1, hαs, hXa, -, -, -, F4⟩ :=
    DA_scalars P.a P.b P.α P.θ s (cDA P) ha hb hα0 hα1 hθ0 hθ1 hs0 (by rw [hs, hμ]) hX
  have hXpos : 0 < cDA P := by
    have : 0 < cDA P * (P.b * (s - P.α)) := by
      rw [hX]; apply mul_pos (by positivity); linarith
    exact pos_of_mul_pos_left this (by have := mul_pos hb (sub_pos.2 hαs); linarith)
  have hbX : P.b * cDA P < P.a * P.α := by rw [lt_div_iff₀ hb] at hXa; linarith
  obtain ⟨-, -, hc1⟩ := oa_alg P hP
  have hW : P.b * what P * (P.α + P.θ) = P.a * P.α * (μ P - P.θ * s) := by
    unfold what; rw [← hsdef]; field_simp
  have hαθ : 0 < P.α + P.θ := by linarith
  refine ⟨hw ▸ hXpos, hw ▸ hbX, ?_, fun c hc hca => ?_, fun c hc => ?_⟩
  · have : P.b * cOA1 P * (P.α + P.θ) = (2 * (P.b * what P) - P.a * P.α) * (P.α + P.θ) := by
      have e : (2 * (P.b * what P) - P.a * P.α) * (P.α + P.θ) =
          2 * (P.b * what P * (P.α + P.θ)) - P.a * P.α * (P.α + P.θ) := by ring
      rw [e, hW]
      have e2 : P.b * cOA1 P * (P.α + P.θ) = cOA1 P * (P.b * (P.α + P.θ)) := by ring
      rw [e2, hc1, ← hsdef]
      linear_combination (-(P.a * P.α)) * hμ
    exact mul_right_cancel₀ hαθ.ne' this
  · -- `s(aα - bc) > α(aμ - bc) > 0`
    have h4 := F4 c
    rw [hs] at h4
    have hpos : 0 < (cDA P - c) * (P.b * (s - P.α)) :=
      mul_pos (by rw [← hw]; linarith) (mul_pos hb (by linarith))
    have hB : 0 < P.α * (P.a * μ P - P.b * c) := by
      apply mul_pos hα0
      have : P.a * P.α < P.a * μ P := by
        apply mul_lt_mul_of_pos_left _ ha; rw [hμ]; nlinarith [mul_pos hθ0 (by linarith : (0:ℝ) < 1 - P.α)]
      linarith
    have hlt : P.α * (P.a * μ P - P.b * c) < s * (P.a * P.α - P.b * c) := by linarith
    have hsq : (P.α * (P.a * μ P - P.b * c)) ^ 2 < (s * (P.a * P.α - P.b * c)) ^ 2 :=
      pow_lt_pow_left₀ hlt hB.le (by norm_num)
    rw [mul_pow, mul_pow, hs] at hsq
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left hsq (by positivity : (0:ℝ) < 8 * P.b)]
  · -- at `ŵ` the inflated order is larger
    obtain ⟨-, -, sw3⟩ := switch_sign P hP (what P)
    have he := sw3 rfl
    rw [k_eq P hP] at he
    unfold g1 g2
    apply mul_lt_mul_of_pos_left _ (by linarith)
    have hw' : 0 < P.a - P.b * (what P / μ P) := by
      have : P.b * (what P / μ P) < P.a := by
        rw [mul_div_assoc', div_lt_iff₀ hμ0]
        have : P.b * what P < P.a * P.α := hw ▸ hbX
        have : P.a * P.α < P.a * μ P := by
          apply mul_lt_mul_of_pos_left _ ha; rw [hμ]; nlinarith [mul_pos hθ0 (by linarith : (0:ℝ) < 1 - P.α)]
        linarith
      linarith
    rw [he, lt_div_iff₀ (by positivity)]
    have : (P.a - P.b * (what P / μ P)) / 2 * (2 * P.α) = P.α * (P.a - P.b * (what P / μ P)) := by ring
    rw [this]
    exact mul_lt_mul_of_pos_right hαs hw'

/-- the quadratic `h` factors through its roots; `c^OA_1` lies strictly between them -/
lemma h_roots (P : Params) (hP : P.Valid) :
    ∃ r1 : ℝ, r1 < cOA1 P ∧ cOA1 P < cOA2 P ∧
      ∀ c, Aq P * c ^ 2 + Bq P * c + Cq P = Aq P * (c - r1) * (c - cOA2 P) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  obtain ⟨hh1, -, -⟩ := oa_alg P hP
  have hA : 0 < Aq P := by unfold Aq; positivity
  set A := Aq P
  set B := Bq P
  set C := Cq P
  set c1 := cOA1 P
  have hD : (2 * A * c1 + B) ^ 2 < B ^ 2 - 4 * A * C := by nlinarith
  have hD0 : 0 < B ^ 2 - 4 * A * C := lt_of_le_of_lt (sq_nonneg _) hD
  set S := Real.sqrt (B ^ 2 - 4 * A * C) with hS
  have hS2 : S ^ 2 = B ^ 2 - 4 * A * C := Real.sq_sqrt hD0.le
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hc2 : cOA2 P = (-B + S) / (2 * A) := cOA2_eq P
  have habs : |2 * A * c1 + B| < S := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) hD
  obtain ⟨hl, hr⟩ := abs_lt.mp habs
  refine ⟨(-B - S) / (2 * A), ?_, ?_, fun c => ?_⟩
  · rw [div_lt_iff₀ (by positivity)]; linarith
  · rw [hc2, lt_div_iff₀ (by positivity)]; linarith
  · rw [hc2]
    field_simp
    linear_combination hS2

end YP3OA


open YieldPostpone.Interplay

namespace YP3OA
open YP3DA YP3L1i

/-- Characterization of the supplier's value and the retailer's response at any admissible `w`
in an SPE of OA. -/
lemma Vchar (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (hσ : IsSPE P c .OA σ) (w : ℝ) (hw : wAdm P c .OA w) :
    (P.b * w < P.a * μ P ∧ what P ≤ w ∧ supplierValue P c .OA σ w = g2 P c w ∧
      σ.q w = (P.a - P.b * (w / μ P)) / 2 ∧ σ.p w = (P.a + P.b * (w / μ P)) / (2 * P.b)) ∨
    (P.b * w < P.a * μ P ∧ w ≤ what P ∧ supplierValue P c .OA σ w = g1 P c w ∧
      σ.q w = (P.a - P.b * (w / P.α)) / (2 * P.α) ∧ σ.p w = (P.a + P.b * (w / P.α)) / (2 * P.b) ∧
      0 < P.a - P.b * (w / P.α)) ∨
    (P.a * μ P ≤ P.b * w ∧ supplierValue P c .OA σ w = 0) := by
  have hq0 : 0 ≤ σ.q w := (hσ.2.2.1 w hw).1
  have hSV : supplierValue P c .OA σ w = (w - c) * σ.q w :=
    sv_OA P c σ w (spe_Q P c σ hσ w _ hw hq0)
  rcases lt_or_ge (P.b * w) (P.a * μ P) with hwa | hwa
  · rcases resp_OA P hP c hc σ hσ w hw hwa with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
    · left; refine ⟨hwa, h3, ?_, h1, h2⟩
      rw [hSV, h1]; rfl
    · rw [k_eq P hP] at h1 h2 h4
      right; left; refine ⟨hwa, h3, ?_, h1, h2, h4⟩
      rw [hSV, h1]; rfl
  · right; right; refine ⟨hwa, ?_⟩
    rw [hSV, resp_zero P hP c hc σ hσ w hw hwa, mul_zero]

/-- generic upper bound on the supplier's value -/
lemma Vbound (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (hσ : IsSPE P c .OA σ) (T : ℝ) (hT : 0 ≤ T)
    (h1 : ∀ w, c < w → w ≤ what P → g1 P c w ≤ T)
    (h2 : ∀ w, c < w → what P ≤ w → P.b * w < P.a * μ P → g2 P c w ≤ T)
    (w : ℝ) (hw : wAdm P c .OA w) : supplierValue P c .OA σ w ≤ T := by
  obtain ⟨hw1, -⟩ := (wAdm_OA P c w).mp hw
  rcases Vchar P hP c hc σ hσ w hw with ⟨a1, a2, a3, -⟩ | ⟨a1, a2, a3, -⟩ | ⟨-, a3⟩
  · rw [a3]; exact h2 w hw1 a2 a1
  · rw [a3]; exact h1 w hw1 a2
  · rw [a3]; exact hT

end YP3OA


open YieldPostpone.Interplay

namespace YP3OA
open YP3DA YP3L1i

/-- the order policy (ties at `ŵ` broken toward the inflated order) -/
noncomputable def qo (P : Params) (w : ℝ) : ℝ :=
  if P.b * w < P.a * μ P then
    (if w ≤ what P then (P.a - P.b * (w / P.α)) / (2 * P.α) else (P.a - P.b * (w / μ P)) / 2)
  else 0

/-- the pricing policy -/
noncomputable def po (P : Params) (w : ℝ) : ℝ :=
  if P.b * w < P.a * μ P then
    (if w ≤ what P then (P.a + P.b * (w / P.α)) / (2 * P.b) else (P.a + P.b * (w / μ P)) / (2 * P.b))
  else P.a / (2 * P.b)

noncomputable def profOA (P : Params) (w : ℝ) : Profile where
  w := w
  Q := fun _ q => q
  q := qo P
  p := po P
  pr := fun _ _ _ => 0

/-- supplier's value along the policy -/
noncomputable def Vp (P : Params) (c w : ℝ) : ℝ :=
  if P.b * w < P.a * μ P then (if w ≤ what P then g1 P c w else g2 P c w) else 0

lemma prof_SV (P : Params) (c w0 w : ℝ) :
    supplierValue P c .OA (profOA P w0) w = Vp P c w := by
  rw [sv_OA P c (profOA P w0) w rfl]
  show (w - c) * qo P w = Vp P c w
  unfold qo Vp g1 g2
  split_ifs <;> ring

/-- the policy response is optimal for the retailer -/
lemma prof_resp (P : Params) (hP : P.Valid) (w0 w : ℝ) (hw0 : 0 < w) (hwab : w < P.a / P.b) :
    0 ≤ qo P w ∧ pAdm P (po P w) ∧
    ∀ q' p', 0 ≤ q' → pAdm P p' →
      retailerProfit P .OA (profOA P w0) w q' p' ≤ retailerProfit P .OA (profOA P w0) w (qo P w) (po P w) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  have hs : Real.sqrt (μ P) ^ 2 = μ P := Real.sq_sqrt hμ0.le
  obtain ⟨-, hwα, -, -, -⟩ := oa_facts P hP
  have hR : ∀ q p, 0 ≤ q → retailerProfit P .OA (profOA P w0) w q p = RN P (w / μ P) q p :=
    fun q p hq => rp_OA P hP (profOA P w0) w q p rfl hq
  have hpa2 : pAdm P (P.a / (2 * P.b)) := by
    rw [pAdm_iff P hb]; refine ⟨by positivity, ?_⟩
    have : P.b * (P.a / (2 * P.b)) = P.a / 2 := by field_simp
    rw [this]; linarith
  rcases lt_or_ge (P.b * w) (P.a * μ P) with hwa | hwa
  · obtain ⟨A1, A2⟩ := Mo_attained P hP w hw0 hwa
    obtain ⟨sw1, sw2, sw3⟩ := switch_sign P hP w
    -- the policy attains `Mo`
    have key : 0 ≤ qo P w ∧ pAdm P (po P w) ∧ RN P (w / μ P) (qo P w) (po P w) = Mo P w := by
      unfold qo po; rw [if_pos hwa, if_pos hwa]
      by_cases hle : w ≤ what P
      · rw [if_pos hle, if_pos hle]
        rcases hle.lt_or_eq with hlt | heq
        · obtain ⟨h1, h2, h3⟩ := A1 (sw1 hlt)
          rw [k_eq P hP] at h1 h2 h3
          exact ⟨h2, h1, h3⟩
        · have he := sw3 heq
          have hak : 0 < P.a - P.b * (w / μ P * μ P / P.α) := by
            rw [k_eq P hP]
            have : P.b * (w / P.α) < P.a := by
              rw [mul_div_assoc', div_lt_iff₀ hα0]; rw [heq]; linarith
            linarith
          have hv := cand2_val P.a P.b P.α P.θ (μ P) (w / μ P) _ hb hα0 hα1 hμ rfl hak
          have hM : Mo P w = μ P * (P.a - P.b * (w / μ P)) ^ 2 / (4 * P.b) := by
            unfold Mo; rw [if_neg (not_lt.mpr he.le)]
          rw [k_eq P hP] at hak hv he
          refine ⟨by positivity, ?_, ?_⟩
          · rw [pAdm_iff P hb]; refine ⟨by positivity, ?_⟩
            have : P.b * ((P.a + P.b * (w / P.α)) / (2 * P.b)) = (P.a + P.b * (w / P.α)) / 2 := by
              field_simp
            rw [this]; linarith
          · unfold RN; rw [hv, hM, he, mul_pow, hs]
      · rw [if_neg hle, if_neg hle]
        push Not at hle
        obtain ⟨h1, h2, h3⟩ := A2 (not_lt.mpr (sw2 hle).le)
        exact ⟨h2, h1, h3⟩
    obtain ⟨k1, k2, k3⟩ := key
    refine ⟨k1, k2, fun q' p' hq' hp' => ?_⟩
    rw [hR _ _ hq', hR _ _ k1, k3]
    exact (RN_le P hP w q' p' hw0 hwa hq' hp').1
  · have hq : qo P w = 0 := by unfold qo; rw [if_neg (not_lt.mpr hwa)]
    have hp : po P w = P.a / (2 * P.b) := by unfold po; rw [if_neg (not_lt.mpr hwa)]
    rw [hq, hp]
    refine ⟨le_rfl, hpa2, fun q' p' hq' hp' => ?_⟩
    rw [hR _ _ hq', hR _ _ le_rfl]
    have hz : RN P (w / μ P) 0 (P.a / (2 * P.b)) = 0 := by
      have hm : min (P.a - P.b * (P.a / (2 * P.b))) 0 = 0 := by
        apply min_eq_right
        have : P.b * (P.a / (2 * P.b)) = P.a / 2 := by field_simp
        rw [this]; linarith
      unfold RN; simp only [mul_zero, hm]; ring
    rw [hz]
    rcases hq'.lt_or_eq with h | h
    · exact (RN_neg P hP w q' p' hwa h hp').le
    · subst h
      have hm : min (P.a - P.b * p') 0 = 0 := by
        obtain ⟨hp0, hpa⟩ := (pAdm_iff P hb p').mp hp'
        exact min_eq_right (by linarith)
      unfold RN; simp only [mul_zero, hm]; ring_nf; exact le_rfl

/-- the policy profile is an SPE as soon as `w0` maximizes `Vp` -/
lemma profOA_spe (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (w0 : ℝ)
    (hw0 : wAdm P c .OA w0) (hmax : ∀ w, wAdm P c .OA w → Vp P c w ≤ Vp P c w0) :
    IsSPE P c .OA (profOA P w0) := by
  refine ⟨fun w q hw hq => ⟨fun h => by simp [Scenario.byDelivery] at h, fun _ => rfl⟩,
    fun h => by simp [Scenario.responsive] at h, fun w hw => ?_, hw0, fun w hw => ?_⟩
  · obtain ⟨hw1, hw2⟩ := (wAdm_OA P c w).mp hw
    obtain ⟨k1, k2, k3⟩ := prof_resp P hP w0 w (by linarith) hw2
    exact ⟨k1, fun _ => k2, fun q' p' hq' hp' => k3 q' p' hq' (hp' rfl)⟩
  · rw [prof_SV, prof_SV]; exact hmax w hw

end YP3OA


open YieldPostpone.Interplay

namespace YP3OA
open YP3DA YP3L1i

lemma CS_OA (P : Params) (c : ℝ) (σ : Profile) :
    CS P c .OA σ =
      P.θ * surplus P (σ.p σ.w) (min (1 * σ.Q σ.w (σ.q σ.w)) (σ.q σ.w)) +
      (1 - P.θ) * surplus P (σ.p σ.w) (min (P.α * σ.Q σ.w (σ.q σ.w)) (σ.q σ.w)) := by
  simp only [CS, E, delivered, Scenario.responsive, Bool.false_eq_true, if_false]

lemma out_cand2 (P : Params) (hP : P.Valid) (c : ℝ) (σ : Profile)
    (hQ : σ.Q σ.w (σ.q σ.w) = σ.q σ.w)
    (hq : σ.q σ.w = (P.a - P.b * (σ.w / P.α)) / (2 * P.α))
    (hp : σ.p σ.w = (P.a + P.b * (σ.w / P.α)) / (2 * P.b))
    (hak : 0 < P.a - P.b * (σ.w / P.α)) :
    piR P c .OA σ = (P.a - P.b * (σ.w / P.α)) ^ 2 / (4 * P.b) ∧
    CS P c .OA σ = ((P.a - P.b * (σ.w / P.α)) / 2) ^ 2 / (2 * P.b) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hq0 : 0 ≤ σ.q σ.w := by rw [hq]; positivity
  constructor
  · show retailerProfit P .OA σ σ.w (σ.q σ.w) (σ.p σ.w) = _
    rw [rp_OA P hP σ _ _ _ hQ hq0, hq, hp, ← k_eq P hP]
    rw [← k_eq P hP] at hak
    exact cand2_val P.a P.b P.α P.θ (μ P) (σ.w / μ P) _ hb hα0 hα1 hμ rfl hak
  · rw [CS_OA, hQ, one_mul]
    have hd : P.a - P.b * σ.p σ.w = (P.a - P.b * (σ.w / P.α)) / 2 := by rw [hp]; field_simp; ring
    have hαq : P.α * σ.q σ.w = (P.a - P.b * (σ.w / P.α)) / 2 := by rw [hq]; field_simp
    have hle : (P.a - P.b * (σ.w / P.α)) / 2 ≤ σ.q σ.w := by
      rw [hq, div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    have hαle : P.α * σ.q σ.w ≤ σ.q σ.w := by nlinarith
    rw [min_self, min_eq_left hαle, surplus_val' P hb _ _ (by rw [hd]; exact hle),
      surplus_val' P hb _ _ (by rw [hd, hαq]), hd]
    ring

lemma out_cand1 (P : Params) (hP : P.Valid) (c : ℝ) (σ : Profile)
    (hQ : σ.Q σ.w (σ.q σ.w) = σ.q σ.w)
    (hq : σ.q σ.w = (P.a - P.b * (σ.w / μ P)) / 2)
    (hp : σ.p σ.w = (P.a + P.b * (σ.w / μ P)) / (2 * P.b))
    (hw' : 0 < P.a - P.b * (σ.w / μ P)) :
    piR P c .OA σ = μ P * (P.a - P.b * (σ.w / μ P)) ^ 2 / (4 * P.b) ∧
    CS P c .OA σ = ((P.a - P.b * (σ.w / μ P)) / 2) ^ 2 / (2 * P.b) *
      (P.α * (2 - P.α) * (1 - P.θ) + P.θ) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hq0 : 0 ≤ σ.q σ.w := by rw [hq]; linarith
  have hwa : P.b * (σ.w / μ P) < P.a := by linarith
  constructor
  · show retailerProfit P .OA σ σ.w (σ.q σ.w) (σ.p σ.w) = _
    rw [rp_OA P hP σ _ _ _ hQ hq0, hq, hp]
    exact cand1_val P.a P.b P.α P.θ (μ P) (σ.w / μ P) hb hα0 hα1 hμ hwa
  · rw [CS_OA, hQ, one_mul]
    have hd : P.a - P.b * σ.p σ.w = σ.q σ.w := by rw [hp, hq]; field_simp; ring
    have hαle : P.α * σ.q σ.w ≤ σ.q σ.w := by nlinarith
    rw [min_self, min_eq_left hαle, surplus_val P hb _ _ (by rw [hd]),
      surplus_val P hb _ _ (by rw [hd]; exact hαle), hd, hq]
    field_simp; ring

lemma Vp_bound (P : Params) (c T : ℝ) (hT : 0 ≤ T)
    (h1 : ∀ w, c < w → w ≤ what P → g1 P c w ≤ T)
    (h2 : ∀ w, c < w → what P < w → P.b * w < P.a * μ P → g2 P c w ≤ T)
    (w : ℝ) (hw : wAdm P c .OA w) : Vp P c w ≤ T := by
  obtain ⟨hw1, -⟩ := (wAdm_OA P c w).mp hw
  unfold Vp
  split_ifs with ha hb'
  · exact h1 w hw1 hb'
  · push Not at hb'; exact h2 w hw1 hb' ha
  · exact hT

end YP3OA


open YieldPostpone.Interplay

namespace YP3OA
open YP3DA YP3L1i

lemma g1_gap (P : Params) (hP : P.Valid) (c w W : ℝ) :
    g1 P c W - g1 P c w = (W - w) * (P.a * P.α + P.b * c - P.b * (W + w)) / (2 * P.α ^ 2) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  unfold g1; field_simp; ring

/-- sign facts on the quadratic `h` and the order `c^OA_2 < ŵ` -/
lemma h_signs (P : Params) (hP : P.Valid) :
    cOA1 P < cOA2 P ∧ cOA2 P < what P ∧
    (∀ c, cOA1 P ≤ c → c < cOA2 P → Aq P * c ^ 2 + Bq P * c + Cq P < 0) ∧
    (∀ c, cOA1 P ≤ c → c ≤ cOA2 P → Aq P * c ^ 2 + Bq P * c + Cq P ≤ 0) ∧
    (∀ c, cOA2 P < c → 0 < Aq P * c ^ 2 + Bq P * c + Cq P) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  have hαμ : P.α < μ P := by rw [hμ]; nlinarith [mul_pos hθ0 (by linarith : (0:ℝ) < 1 - P.α)]
  obtain ⟨r1, hr1, hc12, hfac⟩ := h_roots P hP
  obtain ⟨hW0, hWa, hc1, -, -⟩ := oa_facts P hP
  have hA : 0 < Aq P := by unfold Aq; positivity
  have hc1W : cOA1 P < what P := by
    have : P.b * cOA1 P < P.b * what P := by rw [hc1]; linarith
    exact lt_of_mul_lt_mul_left this hb.le
  refine ⟨hc12, ?_, fun c h1 h2 => ?_, fun c h1 h2 => ?_, fun c h2 => ?_⟩
  · have he := h_eq P hP (what P)
    have hg : g1 P (what P) (what P) = 0 := by unfold g1; ring
    rw [hg, sub_zero] at he
    have hpos : 0 < 8 * P.b * μ P * P.α ^ 2 *
        ((P.a * μ P - P.b * what P) ^ 2 / (8 * P.b * μ P)) := by
      have : 0 < P.a * μ P - P.b * what P := by nlinarith
      positivity
    rw [← he, hfac] at hpos
    have h1 : 0 < what P - r1 := by linarith
    by_contra hn; push Not at hn
    have : Aq P * (what P - r1) * (what P - cOA2 P) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  · rw [hfac]
    exact mul_neg_of_pos_of_neg (mul_pos hA (by linarith)) (by linarith)
  · rw [hfac]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_pos hA (by linarith)).le (by linarith)
  · rw [hfac]
    exact mul_pos (mul_pos hA (by linarith)) (by linarith)

/-- approaching `ŵ` from below along the inflated branch -/
lemma approach (P : Params) (hP : P.Valid) (c v : ℝ) (hc : 0 < c) (hcW : c < what P)
    (hv : v < g1 P c (what P)) :
    ∃ w, c < w ∧ w < what P ∧ v < g1 P c w := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  set W := what P
  set G := g1 P c W
  set K := (P.a * P.α + P.b * c) / (2 * P.α ^ 2) with hK
  have hK0 : 0 < K := by positivity
  set δ := min ((W - c) / 2) ((G - v) / (2 * K)) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (div_pos (by linarith) (by positivity))
  have hδ1 : δ ≤ (W - c) / 2 := min_le_left _ _
  have hδ2 : δ ≤ (G - v) / (2 * K) := min_le_right _ _
  refine ⟨W - δ, by linarith, by linarith, ?_⟩
  have hm := g1_gap P hP c (W - δ) W
  have hb0 : 0 ≤ P.b * (W + (W - δ)) := by
    have : 0 < W := by linarith
    have : 0 < W - δ := by linarith
    positivity
  have h1 : G - g1 P c (W - δ) ≤ δ * K := by
    rw [hm]
    have e : (W - (W - δ)) * (P.a * P.α + P.b * c - P.b * (W + (W - δ))) / (2 * P.α ^ 2) =
        δ * K - δ * (P.b * (W + (W - δ))) / (2 * P.α ^ 2) := by
      rw [hK]; field_simp; ring
    rw [e]
    have : 0 ≤ δ * (P.b * (W + (W - δ))) / (2 * P.α ^ 2) := by positivity
    linarith
  have h2 : δ * K ≤ (G - v) / 2 := by
    have := mul_le_mul_of_nonneg_right hδ2 hK0.le
    have e : (G - v) / (2 * K) * K = (G - v) / 2 := by field_simp
    linarith
  linarith

set_option maxHeartbeats 4000000 in
theorem lemma1_main (P : Params) (hP : P.Valid) :
    cOA1 P < cOA2 P ∧ cOA2 P < P.a * μ P / P.b ∧
    ∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
      (∃ σ : Profile, IsSPE P c .OA σ) ∧
      ∀ σ : Profile, IsSPE P c .OA σ →
        (c < max 0 (cOA1 P) →
          piR P c .OA σ = (P.a * P.α - P.b * c) ^ 2 / (16 * P.b * P.α ^ 2) ∧
          piS P c .OA σ = (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) ∧
          CS P c .OA σ = (P.a * P.α - P.b * c) ^ 2 / (32 * P.b * P.α ^ 2)) ∧
        (max 0 (cOA1 P) < c → c < max 0 (cOA2 P) →
          piR P c .OA σ = (P.a * P.α - P.b * what P) ^ 2 / (4 * P.b * P.α ^ 2) ∧
          piS P c .OA σ = (P.a * P.α - P.b * what P) * (what P - c) / (2 * P.α ^ 2) ∧
          CS P c .OA σ = (P.a * P.α - P.b * what P) ^ 2 / (8 * P.b * P.α ^ 2)) ∧
        (max 0 (cOA2 P) < c →
          piR P c .OA σ = (P.a * μ P - P.b * c) ^ 2 / (16 * P.b * μ P) ∧
          piS P c .OA σ = (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * μ P) ∧
          CS P c .OA σ = (P.a * μ P - P.b * c) ^ 2 *
            (P.α * (2 - P.α) * (1 - P.θ) + P.θ) / (32 * P.b * μ P ^ 2)) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  have hαμ : P.α < μ P := by rw [hμ]; nlinarith [mul_pos hθ0 (by linarith : (0:ℝ) < 1 - P.α)]
  have haαμ : P.a * P.α < P.a * μ P := mul_lt_mul_of_pos_left hαμ ha
  obtain ⟨hW0, hWa, hbc1, hg12m, -⟩ := oa_facts P hP
  obtain ⟨hc12, hc2W, hneg, hle, hpos⟩ := h_signs P hP
  set W := what P with hWdef
  have hc1W : cOA1 P < W := lt_trans hc12 hc2W
  refine ⟨hc12, ?_, fun c hc0 hcμ' => ?_⟩
  · rw [lt_div_iff₀ hb, mul_comm]
    have : P.b * cOA2 P < P.b * W := mul_lt_mul_of_pos_left hc2W hb
    linarith
  have hcμ : P.b * c < P.a * μ P := by rw [lt_div_iff₀ hb] at hcμ'; linarith
  have hPrel : ∀ c, Aq P * c ^ 2 + Bq P * c + Cq P =
      8 * P.b * μ P * P.α ^ 2 * ((P.a * μ P - P.b * c) ^ 2 / (8 * P.b * μ P) - g1 P c W) :=
    fun c => h_eq P hP c
  have hden : 0 < 8 * P.b * μ P * P.α ^ 2 := by positivity
  have hG1le : ∀ w, g1 P c w ≤ (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) := by
    intro w; rw [g1_form P hP]
    have : 0 ≤ P.b / (2 * P.α ^ 2) * (w - (P.a * P.α + P.b * c) / (2 * P.b)) ^ 2 := by positivity
    linarith
  have hG2le : ∀ w, g2 P c w ≤ (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * μ P) := by
    intro w; rw [g2_form P hP]
    have : 0 ≤ P.b / (2 * μ P) * (w - (P.a * μ P + P.b * c) / (2 * P.b)) ^ 2 := by positivity
    linarith
  have hg2pos : 0 < (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * μ P) := by
    have : 0 < P.a * μ P - P.b * c := by linarith
    positivity
  have hmono : cOA1 P ≤ c → ∀ w, w ≤ W → g1 P c w ≤ g1 P c W ∧ (w < W → g1 P c w < g1 P c W) := by
    intro hc1 w hw
    have hm := g1_gap P hP c w W
    have hbc : 2 * P.b * W - P.a * P.α ≤ P.b * c := by
      have := mul_le_mul_of_nonneg_left hc1 hb.le
      linarith
    have hs1 : 0 ≤ P.a * P.α + P.b * c - P.b * (W + w) := by
      have : P.b * w ≤ P.b * W := mul_le_mul_of_nonneg_left hw hb.le
      linarith
    constructor
    · have : 0 ≤ (W - w) * (P.a * P.α + P.b * c - P.b * (W + w)) / (2 * P.α ^ 2) := by
        apply div_nonneg (mul_nonneg (by linarith) hs1) (by positivity)
      linarith
    · intro hlt
      have hs2 : 0 < P.a * P.α + P.b * c - P.b * (W + w) := by
        have : P.b * w < P.b * W := mul_lt_mul_of_pos_left hlt hb
        linarith
      have : 0 < (W - w) * (P.a * P.α + P.b * c - P.b * (W + w)) / (2 * P.α ^ 2) := by
        apply div_pos (mul_pos (by linarith) hs2) (by positivity)
      linarith
  have hG1pos : c < W → 0 < g1 P c W := by
    intro hcW
    unfold g1
    have : P.b * (W / P.α) < P.a := by
      rw [mul_div_assoc', div_lt_iff₀ hα0]; linarith
    have : 0 < P.a - P.b * (W / P.α) := by linarith
    have : 0 < W - c := by linarith
    positivity
  have hwAdm : ∀ w, c < w → P.b * w < P.a → wAdm P c .OA w := by
    intro w h1 h2
    rw [wAdm_OA]; exact ⟨h1, by rw [lt_div_iff₀ hb]; linarith⟩
  set w1 := (P.a * P.α + P.b * c) / (2 * P.b) with hw1
  set w2 := (P.a * μ P + P.b * c) / (2 * P.b) with hw2
  have hbw1 : P.b * w1 = (P.a * P.α + P.b * c) / 2 := by rw [hw1]; field_simp
  have hbw2 : P.b * w2 = (P.a * μ P + P.b * c) / 2 := by rw [hw2]; field_simp
  have hg1w1 : g1 P c w1 = (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) := by
    rw [g1_form P hP, hw1]; ring
  have hg2w2 : g2 P c w2 = (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * μ P) := by
    rw [g2_form P hP, hw2]; ring
  have hcW1 : c < cOA1 P → w1 < W := by
    intro h
    have : P.b * w1 < P.b * W := by
      rw [hbw1]; have := mul_lt_mul_of_pos_left h hb; linarith
    exact lt_of_mul_lt_mul_left this hb.le
  have hW2 : cOA1 P ≤ c → W < w2 := by
    intro h
    have : P.b * W < P.b * w2 := by
      rw [hbw2]; have := mul_le_mul_of_nonneg_left h hb.le; linarith
    exact lt_of_mul_lt_mul_left this hb.le
  have hW1a : P.b * W < P.a := by
    have : P.a * P.α < P.a := by nlinarith
    linarith
  have hVpW : P.b * W < P.a * μ P := by linarith
  -- existence
  constructor
  · by_cases hA : c < cOA1 P
    · have hw1W := hcW1 hA
      have hca : P.b * c < P.a * P.α := by
        have : P.b * c < P.b * W := mul_lt_mul_of_pos_left (lt_trans hA hc1W) hb
        linarith
      have hadm : wAdm P c .OA w1 := hwAdm w1 (by
          have : P.b * c < P.b * w1 := by rw [hbw1]; linarith
          exact lt_of_mul_lt_mul_left this hb.le) (by rw [hbw1]; nlinarith)
      have hV1 : Vp P c w1 = (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) := by
        unfold Vp; rw [if_pos (by rw [hbw1]; linarith), if_pos hw1W.le, hg1w1]
      refine ⟨_, profOA_spe P hP c hc0 w1 hadm (fun w hw => ?_)⟩
      rw [hV1]
      apply Vp_bound P c _ (by positivity) (fun w _ _ => hG1le w) (fun w _ _ _ => ?_) w hw
      exact le_trans (hG2le w) (hg12m c (lt_trans hA hc1W) hca).le
    · push Not at hA
      by_cases hB : c ≤ cOA2 P
      · have hcW : c < W := lt_of_le_of_lt hB hc2W
        have hadm : wAdm P c .OA W := hwAdm W hcW hW1a
        have hVW : Vp P c W = g1 P c W := by
          unfold Vp; rw [if_pos hVpW, if_pos le_rfl]
        refine ⟨_, profOA_spe P hP c hc0 W hadm (fun w hw => ?_)⟩
        rw [hVW]
        apply Vp_bound P c _ (hG1pos hcW).le (fun w _ h => (hmono hA w h).1) (fun w _ _ _ => ?_) w hw
        have h3 := hle c hA hB
        rw [hPrel] at h3
        have : (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * μ P) - g1 P c W ≤ 0 := by
          by_contra hh; push Not at hh
          have := mul_pos hden hh; linarith
        linarith [hG2le w]
      · push Not at hB
        have hW2' := hW2 hA
        have hadm : wAdm P c .OA w2 := hwAdm w2 (by
            have : P.b * c < P.b * w2 := by rw [hbw2]; linarith
            exact lt_of_mul_lt_mul_left this hb.le) (by rw [hbw2]; nlinarith)
        have hV2 : Vp P c w2 = (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * μ P) := by
          unfold Vp; rw [if_pos (by rw [hbw2]; linarith), if_neg (not_le.mpr hW2'), hg2w2]
        refine ⟨_, profOA_spe P hP c hc0 w2 hadm (fun w hw => ?_)⟩
        rw [hV2]
        apply Vp_bound P c _ hg2pos.le (fun w _ h => ?_) (fun w _ _ _ => hG2le w) w hw
        have h3 := hpos c hB
        rw [hPrel] at h3
        have : 0 < (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * μ P) - g1 P c W := by
          by_contra hh; push Not at hh
          have := mul_nonpos_of_nonneg_of_nonpos hden.le hh; linarith
        linarith [(hmono hA w h).1]
  -- uniqueness
  intro σ hσ
  have hopt : ∀ w, wAdm P c .OA w → supplierValue P c .OA σ w ≤ supplierValue P c .OA σ σ.w :=
    hσ.2.2.2.2
  have hwσ : wAdm P c .OA σ.w := hσ.2.2.2.1
  have hQ : σ.Q σ.w (σ.q σ.w) = σ.q σ.w := spe_Q P c σ hσ σ.w _ hwσ (hσ.2.2.1 σ.w hwσ).1
  have hV := fun w hw => Vchar P hP c hc0 σ hσ w hw
  have hpiS : piS P c .OA σ = supplierValue P c .OA σ σ.w := rfl
  refine ⟨fun hA => ?_, fun hB1 hB2 => ?_, fun hC => ?_⟩
  · -- low cost: the inflated optimum `w₁`
    have hA' : c < cOA1 P := by
      rcases le_total 0 (cOA1 P) with h | h
      · rwa [max_eq_right h] at hA
      · rw [max_eq_left h] at hA; linarith
    have hw1W := hcW1 hA'
    have hca : P.b * c < P.a * P.α := by
      have : P.b * c < P.b * W := mul_lt_mul_of_pos_left (lt_trans hA' hc1W) hb
      linarith
    have hadm : wAdm P c .OA w1 := hwAdm w1 (by
        have : P.b * c < P.b * w1 := by rw [hbw1]; linarith
        exact lt_of_mul_lt_mul_left this hb.le) (by rw [hbw1]; nlinarith)
    have hg1pos : 0 < (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) := by
      have : 0 < P.a * P.α - P.b * c := by linarith
      positivity
    have hVw1 : supplierValue P c .OA σ w1 = (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) := by
      rcases hV w1 hadm with ⟨-, h, -⟩ | ⟨-, -, h, -⟩ | ⟨h, -⟩
      · exfalso; linarith
      · rw [h, hg1w1]
      · exfalso; rw [hbw1] at h; linarith
    have hge := hopt w1 hadm
    rw [hVw1] at hge
    rcases hV σ.w hwσ with ⟨-, -, h, -⟩ | ⟨hwa, -, h, hq, hp, hak⟩ | ⟨-, h⟩
    · rw [h] at hge; linarith [hG2le σ.w, hg12m c (lt_trans hA' hc1W) hca]
    · rw [h, g1_form P hP] at hge
      have hsq : (σ.w - (P.a * P.α + P.b * c) / (2 * P.b)) ^ 2 = 0 := by
        have : 0 ≤ P.b / (2 * P.α ^ 2) * (σ.w - (P.a * P.α + P.b * c) / (2 * P.b)) ^ 2 := by
          positivity
        have h0 : P.b / (2 * P.α ^ 2) * (σ.w - (P.a * P.α + P.b * c) / (2 * P.b)) ^ 2 = 0 := by
          linarith
        rcases mul_eq_zero.mp h0 with h' | h'
        · exfalso; have : 0 < P.b / (2 * P.α ^ 2) := by positivity
          linarith
        · exact h'
      have hws : σ.w = w1 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
        rw [hw1]; linarith
      obtain ⟨e1, e3⟩ := out_cand2 P hP c σ hQ hq hp hak
      have e2 : piS P c .OA σ = g1 P c σ.w := by rw [hpiS, h]
      rw [e1, e2, e3, hws, hg1w1, hw1]
      refine ⟨?_, rfl, ?_⟩ <;> field_simp <;> ring
    · rw [h] at hge; linarith
  · -- middle cost: the kink price `ŵ` with the inflated response
    have hc1 : cOA1 P < c := lt_of_le_of_lt (le_max_right _ _) hB1
    have hc2 : c < cOA2 P := by
      rcases le_total 0 (cOA2 P) with h | h
      · rwa [max_eq_right h] at hB2
      · rw [max_eq_left h] at hB2; linarith
    have hcW : c < W := lt_trans hc2 hc2W
    have hgap : (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * μ P) < g1 P c W := by
      have h3 := hneg c hc1.le hc2
      rw [hPrel] at h3
      have : (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * μ P) - g1 P c W < 0 := by
        by_contra hh; push Not at hh
        have := mul_nonneg hden.le hh; linarith
      linarith
    have hVge : g1 P c W ≤ supplierValue P c .OA σ σ.w := by
      by_contra hlt; push Not at hlt
      obtain ⟨w, hcw, hwW, hv⟩ := approach P hP c _ hc0 hcW hlt
      have hadmw : wAdm P c .OA w := hwAdm w hcw (by
        have : P.b * w < P.b * W := mul_lt_mul_of_pos_left hwW hb
        linarith)
      have h1 := hopt w hadmw
      rcases hV w hadmw with ⟨-, h, -⟩ | ⟨-, -, h, -⟩ | ⟨h, -⟩
      · exfalso; linarith
      · rw [h] at h1; linarith
      · exfalso
        have : P.b * w < P.b * W := mul_lt_mul_of_pos_left hwW hb
        linarith
    rcases hV σ.w hwσ with ⟨-, -, h, -⟩ | ⟨hwa, hwle, h, hq, hp, hak⟩ | ⟨-, h⟩
    · rw [h] at hVge; linarith [hG2le σ.w]
    · have hws : σ.w = W := by
        by_contra hne
        have := (hmono hc1.le σ.w hwle).2 (lt_of_le_of_ne hwle hne)
        rw [h] at hVge; linarith
      obtain ⟨e1, e3⟩ := out_cand2 P hP c σ hQ hq hp hak
      have e2 : piS P c .OA σ = g1 P c σ.w := by rw [hpiS, h]
      rw [e1, e2, e3, hws]
      unfold g1
      refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring
    · rw [h] at hVge; linarith [hG1pos hcW]
  · -- high cost: the non-inflated optimum `w₂`
    have hC' : cOA2 P < c := lt_of_le_of_lt (le_max_right _ _) hC
    have hc1 : cOA1 P ≤ c := by linarith
    have hW2' := hW2 hc1
    have hadm : wAdm P c .OA w2 := hwAdm w2 (by
        have : P.b * c < P.b * w2 := by rw [hbw2]; linarith
        exact lt_of_mul_lt_mul_left this hb.le) (by rw [hbw2]; nlinarith)
    have hVw2 : supplierValue P c .OA σ w2 = (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * μ P) := by
      rcases hV w2 hadm with ⟨-, -, h, -⟩ | ⟨-, h, -⟩ | ⟨h, -⟩
      · rw [h, hg2w2]
      · exfalso; linarith
      · exfalso; rw [hbw2] at h; linarith
    have hge := hopt w2 hadm
    rw [hVw2] at hge
    have hgap : g1 P c W < (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * μ P) := by
      have h3 := hpos c hC'
      rw [hPrel] at h3
      have : 0 < (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * μ P) - g1 P c W := by
        by_contra hh; push Not at hh
        have := mul_nonpos_of_nonneg_of_nonpos hden.le hh; linarith
      linarith
    rcases hV σ.w hwσ with ⟨hwa, -, h, hq, hp⟩ | ⟨-, hwle, h, -⟩ | ⟨-, h⟩
    · rw [h, g2_form P hP] at hge
      have hsq : (σ.w - (P.a * μ P + P.b * c) / (2 * P.b)) ^ 2 = 0 := by
        have : 0 ≤ P.b / (2 * μ P) * (σ.w - (P.a * μ P + P.b * c) / (2 * P.b)) ^ 2 := by
          positivity
        have h0 : P.b / (2 * μ P) * (σ.w - (P.a * μ P + P.b * c) / (2 * P.b)) ^ 2 = 0 := by
          linarith
        rcases mul_eq_zero.mp h0 with h' | h'
        · exfalso; have : 0 < P.b / (2 * μ P) := by positivity
          linarith
        · exact h'
      have hws : σ.w = w2 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
        rw [hw2]; linarith
      have hpos2 : 0 < P.a - P.b * (σ.w / μ P) := by
        rw [hws, mul_div_assoc', sub_pos, div_lt_iff₀ hμ0, hbw2]; linarith
      obtain ⟨e1, e3⟩ := out_cand1 P hP c σ hQ hq hp hpos2
      have e2 : piS P c .OA σ = g2 P c σ.w := by rw [hpiS, h]
      rw [e1, e2, e3, hws, hg2w2, hw2]
      refine ⟨?_, rfl, ?_⟩ <;> field_simp <;> ring
    · rw [h] at hge; linarith [(hmono hc1 σ.w hwle).1]
    · rw [h] at hge; linarith

end YP3OA

open YieldPostpone.Interplay

theorem solution (P : Params) (hP : P.Valid) :
    cOA1 P < cOA2 P ∧ cOA2 P < P.a * μ P / P.b ∧
    ∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
      (∃ σ : Profile, IsSPE P c .OA σ) ∧
      ∀ σ : Profile, IsSPE P c .OA σ →
        (c < max 0 (cOA1 P) →
          piR P c .OA σ = (P.a * P.α - P.b * c) ^ 2 / (16 * P.b * P.α ^ 2) ∧
          piS P c .OA σ = (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) ∧
          CS P c .OA σ = (P.a * P.α - P.b * c) ^ 2 / (32 * P.b * P.α ^ 2)) ∧
        (max 0 (cOA1 P) < c → c < max 0 (cOA2 P) →
          piR P c .OA σ = (P.a * P.α - P.b * what P) ^ 2 / (4 * P.b * P.α ^ 2) ∧
          piS P c .OA σ = (P.a * P.α - P.b * what P) * (what P - c) / (2 * P.α ^ 2) ∧
          CS P c .OA σ = (P.a * P.α - P.b * what P) ^ 2 / (8 * P.b * P.α ^ 2)) ∧
        (max 0 (cOA2 P) < c →
          piR P c .OA σ = (P.a * μ P - P.b * c) ^ 2 / (16 * P.b * μ P) ∧
          piS P c .OA σ = (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * μ P) ∧
          CS P c .OA σ = (P.a * μ P - P.b * c) ^ 2 *
            (P.α * (2 - P.α) * (1 - P.θ) + P.θ) / (32 * P.b * μ P ^ 2)) :=
  YP3OA.lemma1_main P hP
