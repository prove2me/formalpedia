-- Prove2me | solution 1 for YieldPostpone.Payment.lemma_1_corrected
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T04:57:46.285814+00:00
-- url     : https://prove2.me/submissions/42c0243e-ab80-43c3-ad64-376c596b672d

import Definitions.Def_YieldPostpone_Payment_ClosedForms

open YieldPostpone.Payment

namespace PPL3

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

end PPL3


open YieldPostpone.Payment

namespace PPL3

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

end PPL3

namespace PPL3

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


end PPL3


open YieldPostpone.Payment

namespace PPL1

open PPL3

lemma wAdm_OA (P : Params) (c w : ℝ) : wAdm P c .OA w ↔ c < w ∧ w < P.a / P.b := by
  simp [wAdm, Scenario.byDelivery]

lemma isSPE_OA (P : Params) (c : ℝ) (σ : Profile) :
    IsSPE P c .OA σ ↔
      (∀ w q, σ.Q w q = q) ∧ True ∧
      (∀ w, wAdm P c .OA w →
        0 ≤ σ.q w ∧ pAdm P (σ.p w) ∧
        ∀ q' p', 0 ≤ q' → pAdm P p' →
          retailerProfit P .OA σ w q' p' ≤ retailerProfit P .OA σ w (σ.q w) (σ.p w)) ∧
      wAdm P c .OA σ.w ∧
      ∀ w', wAdm P c .OA w' → supplierValue P c .OA σ w' ≤ supplierValue P c .OA σ σ.w :=
  Iff.rfl

lemma rp_OA (P : Params) (hP : P.Valid) (σ : Profile) (w q p : ℝ) (hq : 0 ≤ q)
    (hQ : σ.Q w q = q) :
    retailerProfit P .OA σ w q p =
      P.θ * (p * min (P.a - P.b * p) q - w * q) +
        (1 - P.θ) * (p * min (P.a - P.b * p) (P.α * q) - w * q) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hαq : P.α * q ≤ q := by nlinarith
  simp only [retailerProfit, E, transfer, delivered, salesRev, demand, Scenario.byDelivery,
    Scenario.responsive, Bool.false_eq_true, if_false, one_mul, hQ, min_self, min_eq_left hαq]

lemma rp_RL (θ α μ w p q m1 m2 : ℝ) (hμ : μ = α * (1 - θ) + θ) (hμ0 : 0 < μ) :
    θ * (p * m1 - w * q) + (1 - θ) * (p * m2 - w * q) =
      θ * (p * m1 - w / μ * q) + (1 - θ) * (p * m2 - w / μ * (α * q)) := by
  have e : θ * (w / μ * q) + (1 - θ) * (w / μ * (α * q)) = w * q := by
    rw [show θ * (w / μ * q) + (1 - θ) * (w / μ * (α * q)) = w / μ * q * (α * (1 - θ) + θ) by ring,
      ← hμ]
    field_simp
  linear_combination e

lemma CS_OA (P : Params) (hP : P.Valid) (c : ℝ) (σ : Profile) (hQ : ∀ w q, σ.Q w q = q)
    (hq : 0 ≤ σ.q σ.w) :
    CS P c .OA σ = P.θ * surplus P (σ.p σ.w) (σ.q σ.w) +
      (1 - P.θ) * surplus P (σ.p σ.w) (P.α * σ.q σ.w) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hαq : P.α * σ.q σ.w ≤ σ.q σ.w := by nlinarith
  simp only [CS, E, delivered, Scenario.responsive, Bool.false_eq_true, if_false, one_mul, hQ,
    min_self, min_eq_left hαq]

/-- the retailer's optimum under OA: one of two candidates (`w < a μ / b`) -/
lemma resp_OA (P : Params) (hP : P.Valid) (c : ℝ) (σ : Profile)
    (hσ : IsSPE P c .OA σ) (w : ℝ) (hw : wAdm P c .OA w) (hc : 0 < c)
    (hwa : P.b * w < P.a * P.μ) :
    let w1 := w / P.μ
    let k := w1 * P.μ / P.α
    let M := if Real.sqrt P.μ * (P.a - P.b * w1) < P.a - P.b * k then
      (P.a - P.b * k) ^ 2 / (4 * P.b) else P.μ * (P.a - P.b * w1) ^ 2 / (4 * P.b)
    retailerProfit P .OA σ w (σ.q w) (σ.p w) = M ∧
    ((σ.q w = (P.a - P.b * w1) / 2 ∧ σ.p w = (P.a + P.b * w1) / (2 * P.b) ∧
        M = P.μ * (P.a - P.b * w1) ^ 2 / (4 * P.b)) ∨
      (σ.q w = (P.a - P.b * k) / (2 * P.α) ∧ σ.p w = (P.a + P.b * k) / (2 * P.b) ∧
        M = (P.a - P.b * k) ^ 2 / (4 * P.b) ∧ 0 < P.a - P.b * k)) := by
  intro w1 k M
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < P.μ := by
    rw [hμ]
    have : 0 < 1 - P.θ := by linarith
    positivity
  have hs0 : 0 < Real.sqrt P.μ := Real.sqrt_pos.mpr hμ0
  have hs : Real.sqrt P.μ ^ 2 = P.μ := Real.sq_sqrt hμ0.le
  obtain ⟨hw1, hw2⟩ := (wAdm_OA P c w).mp hw
  have hw0 : 0 < w := lt_trans hc hw1
  have hw10 : 0 < w1 := div_pos hw0 hμ0
  have hw1a : P.b * w1 < P.a := by
    show P.b * (w / P.μ) < P.a
    rw [mul_div_assoc', div_lt_iff₀ hμ0]; linarith
  obtain ⟨hQ, -, hret, -, -⟩ := (isSPE_OA P c σ).mp hσ
  obtain ⟨hq0, hpA, hopt⟩ := hret w hw
  have hk : k = w1 * P.μ / P.α := rfl
  have hM : M = if Real.sqrt P.μ * (P.a - P.b * w1) < P.a - P.b * k then
      (P.a - P.b * k) ^ 2 / (4 * P.b) else P.μ * (P.a - P.b * w1) ^ 2 / (4 * P.b) := rfl
  have hRP : ∀ q p, 0 ≤ q → retailerProfit P .OA σ w q p =
      P.θ * (p * min (P.a - P.b * p) q - w1 * q) +
        (1 - P.θ) * (p * min (P.a - P.b * p) (P.α * q) - w1 * (P.α * q)) := by
    intro q p hq
    rw [rp_OA P hP σ w q p hq (hQ w q)]
    exact rp_RL P.θ P.α P.μ w p q _ _ hμ hμ0
  have hcand : M ≤ retailerProfit P .OA σ w (σ.q w) (σ.p w) := by
    by_cases hC : Real.sqrt P.μ * (P.a - P.b * w1) < P.a - P.b * k
    · have hak : 0 < P.a - P.b * k := lt_trans (by
        have : 0 < P.a - P.b * w1 := by linarith
        positivity) hC
      have hq2 : 0 ≤ (P.a - P.b * k) / (2 * P.α) := by positivity
      have hp2A : pAdm P ((P.a + P.b * k) / (2 * P.b)) := by
        rw [pAdm_iff P hb]
        have hk0 : 0 < k := by rw [hk]; positivity
        refine ⟨by positivity, ?_⟩
        have : P.b * ((P.a + P.b * k) / (2 * P.b)) = (P.a + P.b * k) / 2 := by
          field_simp
        rw [this]; linarith
      have h1 := hopt _ _ hq2 hp2A
      rw [hRP _ _ hq2, cand2_val P.a P.b P.α P.θ P.μ w1 k hb hα0 hα1 hμ hk hak] at h1
      rw [hM, if_pos hC]; exact h1
    · have hq1 : 0 ≤ (P.a - P.b * w1) / 2 := by linarith
      have hp1A : pAdm P ((P.a + P.b * w1) / (2 * P.b)) := by
        rw [pAdm_iff P hb]
        refine ⟨by positivity, ?_⟩
        have : P.b * ((P.a + P.b * w1) / (2 * P.b)) = (P.a + P.b * w1) / 2 := by field_simp
        rw [this]; linarith
      have h1 := hopt _ _ hq1 hp1A
      rw [hRP _ _ hq1, cand1_val P.a P.b P.α P.θ P.μ w1 hb hα0 hα1 hμ hw1a] at h1
      rw [hM, if_neg hC]; exact h1
  obtain ⟨hp0, hpa⟩ := (pAdm_iff P hb _).mp hpA
  have hRL := RL_le P.a P.b P.α P.θ P.μ (Real.sqrt P.μ) w1 (σ.q w) (σ.p w) k M
    hb hα0 hα1 hθ0 hθ1 hμ hs0 hs hw10 hw1a hq0 hp0 hpa hk hM
  rw [hRP _ _ hq0] at hcand ⊢
  obtain ⟨hle, heq⟩ := hRL
  have he := le_antisymm hle hcand
  exact ⟨he, heq he⟩

/-- profits are nonpositive when `w ≥ a μ / b` -/
lemma rp_nonpos (P : Params) (hP : P.Valid) (σ : Profile) (w q p : ℝ) (hq : 0 ≤ q)
    (hQ : σ.Q w q = q) (hp : pAdm P p) (hwa : P.a * P.μ ≤ P.b * w) :
    retailerProfit P .OA σ w q p ≤ 0 := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  obtain ⟨hp0, hpa⟩ := (pAdm_iff P hb _).mp hp
  rw [rp_OA P hP σ w q p hq hQ]
  have h1 : min (P.a - P.b * p) q ≤ q := min_le_right _ _
  have h2 : min (P.a - P.b * p) (P.α * q) ≤ P.α * q := min_le_right _ _
  have h3 : P.θ * (p * min (P.a - P.b * p) q) ≤ P.θ * (p * q) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hp0.le) hθ0.le
  have h4 : (1 - P.θ) * (p * min (P.a - P.b * p) (P.α * q)) ≤ (1 - P.θ) * (p * (P.α * q)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hp0.le) (by linarith)
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
  have h5 : P.μ * p * P.b ≤ P.b * w := by
    have : P.μ * (P.b * p) ≤ P.μ * P.a := by
      apply mul_le_mul_of_nonneg_left hpa.le
      rw [hμ]; have : 0 < 1 - P.θ := by linarith
      positivity
    nlinarith
  have h6 : P.μ * p ≤ w := by
    by_contra h; push Not at h
    have := mul_lt_mul_of_pos_right h hb
    linarith
  have h7 : (P.μ * p - w) * q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hq
  rw [hμ] at h7
  nlinarith

/-- in any OA equilibrium, profit and consumer surplus are tied by one of two relations -/
lemma oa_rel (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (hσ : IsSPE P c .OA σ) :
    piR P c .OA σ ≤ 0 ∨ 2 * CS P c .OA σ = piR P c .OA σ ∨
      2 * P.μ * CS P c .OA σ = (P.α * (2 - P.α) * (1 - P.θ) + P.θ) * piR P c .OA σ := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  obtain ⟨hQ, -, hret, hw, -⟩ := (isSPE_OA P c σ).mp hσ
  obtain ⟨hq0, hpA, -⟩ := hret σ.w hw
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < P.μ := by
    rw [hμ]; have : 0 < 1 - P.θ := by linarith
    positivity
  have hpiR : piR P c .OA σ = retailerProfit P .OA σ σ.w (σ.q σ.w) (σ.p σ.w) := rfl
  rcases le_or_gt (P.a * P.μ) (P.b * σ.w) with hwa | hwa
  · left
    rw [hpiR]
    exact rp_nonpos P hP σ σ.w _ _ hq0 (hQ _ _) hpA hwa
  right
  obtain ⟨hR, hcases⟩ := resp_OA P hP c σ hσ σ.w hw hc hwa
  rw [hpiR, hR, CS_OA P hP c σ hQ hq0, surplus_eq P hb, surplus_eq P hb]
  rcases hcases with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3, hak⟩
  · right
    rw [e3, e1, e2]
    set w1 := σ.w / P.μ
    have hd : P.a - P.b * ((P.a + P.b * w1) / (2 * P.b)) = (P.a - P.b * w1) / 2 := by
      field_simp; ring
    have hw1a : P.b * w1 < P.a := by
      show P.b * (σ.w / P.μ) < P.a
      rw [mul_div_assoc', div_lt_iff₀ hμ0]; linarith
    have hq : 0 ≤ (P.a - P.b * w1) / 2 := by linarith
    have hαq : P.α * ((P.a - P.b * w1) / 2) ≤ (P.a - P.b * w1) / 2 := by nlinarith
    rw [hd, min_self, min_eq_right hαq, hμ]
    field_simp
    ring
  · left
    rw [e3, e1, e2]
    set k := σ.w / P.μ * P.μ / P.α
    have hd : P.a - P.b * ((P.a + P.b * k) / (2 * P.b)) = (P.a - P.b * k) / 2 := by
      field_simp; ring
    have hαq : P.α * ((P.a - P.b * k) / (2 * P.α)) = (P.a - P.b * k) / 2 := by field_simp
    have hle : (P.a - P.b * k) / 2 ≤ (P.a - P.b * k) / (2 * P.α) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    rw [hd, hαq, min_self, min_eq_left hle]
    field_simp
    ring

end PPL1


open YieldPostpone.Payment

namespace PPL1

set_option maxHeartbeats 2000000 in
/-- Generic facts about `ŵ`, `c₁ = 2ŵ - aα/b` and the quadratic `Φ` defining `c₂`. -/
lemma phi_facts (a b α θ s W : ℝ) (ha : 0 < a) (hb : 0 < b) (hα0 : 0 < α) (hα1 : α < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs0 : 0 < s) (hs : s ^ 2 = α * (1 - θ) + θ)
    (hW : W * (b * (s - α)) = a * α * s * (1 - s)) :
    let c1 := 2 * W - a * α / b
    let A := α ^ 2 * b ^ 2
    let B := -(2 * α ^ 2 * a * s ^ 2 * b) + 4 * b * s ^ 2 * (a * α - b * W)
    let C := α ^ 2 * (a * s ^ 2) ^ 2 - 4 * b * s ^ 2 * (a * α - b * W) * W
    let c2 := (-B + Real.sqrt (B ^ 2 - 4 * A * C)) / (2 * A)
    α < s ∧ s < 1 ∧ 0 < W ∧ b * W < a * α ∧ c1 < W ∧ c1 < c2 ∧ c2 < W ∧
    (∀ c, α ^ 2 * (a * s ^ 2 - b * c) ^ 2 - 4 * b * s ^ 2 * (a * α - b * W) * (W - c) =
      A * c ^ 2 + B * c + C) ∧
    (∀ c, c1 ≤ c → c < c2 → A * c ^ 2 + B * c + C < 0) ∧
    (∀ c, c1 ≤ c → c ≤ c2 → A * c ^ 2 + B * c + C ≤ 0) ∧
    (∀ c, c2 < c → 0 < A * c ^ 2 + B * c + C) ∧
    (∀ c, s * (a * α - b * c) - α * (a * s ^ 2 - b * c) = (W - c) * (b * (s - α))) := by
  intro c1 A B C c2
  have hc1def : c1 = 2 * W - a * α / b := rfl
  have hAdef : A = α ^ 2 * b ^ 2 := rfl
  have hBdef : B = -(2 * α ^ 2 * a * s ^ 2 * b) + 4 * b * s ^ 2 * (a * α - b * W) := rfl
  have hCdef : C = α ^ 2 * (a * s ^ 2) ^ 2 - 4 * b * s ^ 2 * (a * α - b * W) * W := rfl
  have hc2def : c2 = (-B + Real.sqrt (B ^ 2 - 4 * A * C)) / (2 * A) := rfl
  clear_value c1 A B C c2
  have h1θ : 0 < 1 - θ := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hαs2 : α < s ^ 2 := by rw [hs]; nlinarith [mul_pos hθ0 h1α]
  have hs21 : s ^ 2 < 1 := by rw [hs]; nlinarith [mul_pos h1θ h1α]
  have hs1 : s < 1 := by nlinarith
  have hαs : α < s := by nlinarith
  have hsα : 0 < s - α := by linarith
  have hbsα : 0 < b * (s - α) := by positivity
  have hW0 : 0 < W := by
    have : 0 < W * (b * (s - α)) := by
      rw [hW]; have : 0 < 1 - s := by linarith
      positivity
    exact pos_of_mul_pos_left this hbsα.le
  have hWa : b * W < a * α := by
    have h1 : W * (b * (s - α)) < a * α * (s - α) := by
      rw [hW]
      have : s * (1 - s) < s - α := by nlinarith
      have := mul_lt_mul_of_pos_left this (by positivity : 0 < a * α)
      linarith
    nlinarith
  have hc1W : c1 < W := by
    rw [hc1def]
    have : W < a * α / b := by rw [lt_div_iff₀ hb]; linarith
    linarith
  have hlin : ∀ c, s * (a * α - b * c) - α * (a * s ^ 2 - b * c) = (W - c) * (b * (s - α)) := by
    intro c
    have : (W - c) * (b * (s - α)) = W * (b * (s - α)) - c * (b * (s - α)) := by ring
    rw [this, hW]; ring
  have hA : 0 < A := by rw [hAdef]; positivity
  have hPhi : ∀ c, α ^ 2 * (a * s ^ 2 - b * c) ^ 2 - 4 * b * s ^ 2 * (a * α - b * W) * (W - c) =
      A * c ^ 2 + B * c + C := by
    intro c; rw [hAdef, hBdef, hCdef]; ring
  -- Φ(c₁) < 0
  have hPc1 : A * c1 ^ 2 + B * c1 + C < 0 := by
    rw [← hPhi]
    have hbc1 : b * c1 = 2 * b * W - a * α := by
      rw [hc1def]; field_simp
    have e : a * α - b * W = (a * α - b * c1) / 2 := by linarith
    have hk : 0 < a * α - b * c1 := by linarith
    have h2 : α * (a * s ^ 2 - b * c1) < s * (a * α - b * c1) := by
      have := hlin c1
      have : 0 < (W - c1) * (b * (s - α)) := mul_pos (by linarith) hbsα
      linarith
    have h3 : 0 < α * (a * s ^ 2 - b * c1) := by
      have : b * c1 < a * s ^ 2 := by nlinarith
      have : 0 < a * s ^ 2 - b * c1 := by linarith
      positivity
    have h4 : (α * (a * s ^ 2 - b * c1)) ^ 2 < (s * (a * α - b * c1)) ^ 2 := by nlinarith
    have hWc : W - c1 = (a * α - b * c1) / (2 * b) := by
      field_simp; linarith
    rw [e, hWc]
    have e2 : 4 * b * s ^ 2 * ((a * α - b * c1) / 2) * ((a * α - b * c1) / (2 * b)) =
        (s * (a * α - b * c1)) ^ 2 := by field_simp; ring
    rw [e2]
    have e3 : α ^ 2 * (a * s ^ 2 - b * c1) ^ 2 = (α * (a * s ^ 2 - b * c1)) ^ 2 := by ring
    rw [e3]
    linarith
  have hdisc : 0 < B ^ 2 - 4 * A * C := by
    have h1 : 4 * A * (A * c1 ^ 2 + B * c1 + C) = (2 * A * c1 + B) ^ 2 - (B ^ 2 - 4 * A * C) := by
      ring
    have h5 : 4 * A * (A * c1 ^ 2 + B * c1 + C) < 0 := mul_neg_of_pos_of_neg (by linarith) hPc1
    rw [h1] at h5
    linarith [sq_nonneg (2 * A * c1 + B)]
  set S := Real.sqrt (B ^ 2 - 4 * A * C) with hS
  have hS0 : 0 < S := Real.sqrt_pos.mpr hdisc
  have hS2 : S ^ 2 = B ^ 2 - 4 * A * C := Real.sq_sqrt hdisc.le
  have hc2 : 2 * A * c2 + B = S := by
    rw [hc2def]; field_simp; ring
  clear_value S
  clear hc2def hS
  have hfac : ∀ c, 4 * A * (A * c ^ 2 + B * c + C) = (2 * A * c + B - S) * (2 * A * c + B + S) := by
    intro c; linear_combination hS2
  have hneg1 : (2 * A * c1 + B - S) * (2 * A * c1 + B + S) < 0 := by
    rw [← hfac]; exact mul_neg_of_pos_of_neg (by linarith) hPc1
  have hc1pos : 0 < 2 * A * c1 + B + S := by
    by_contra hn; push Not at hn
    have h1 : 2 * A * c1 + B - S ≤ 0 := by linarith
    have := mul_nonneg_of_nonpos_of_nonpos h1 hn
    linarith
  have hc1m : 2 * A * c1 + B - S < 0 := by
    by_contra hn; push Not at hn
    have := mul_nonneg hn hc1pos.le
    linarith
  have h2A : 0 < 2 * A := by linarith
  have hc1c2 : c1 < c2 := by
    have : 2 * A * c1 < 2 * A * c2 := by linarith
    exact lt_of_mul_lt_mul_left this h2A.le
  have hsign : ∀ c, c1 ≤ c → 0 < 2 * A * c + B + S := by
    intro c hc
    have : 2 * A * c1 ≤ 2 * A * c := mul_le_mul_of_nonneg_left hc h2A.le
    linarith
  have hPW : 0 < A * W ^ 2 + B * W + C := by
    rw [← hPhi]
    have : 0 < a * s ^ 2 - b * W := by
      have : a * α < a * s ^ 2 := mul_lt_mul_of_pos_left hαs2 ha
      linarith
    have e : W - W = 0 := by ring
    rw [e, mul_zero, sub_zero]
    positivity
  have hc2W : c2 < W := by
    have h2 := hsign W hc1W.le
    have hp : 0 < (2 * A * W + B - S) * (2 * A * W + B + S) := by
      rw [← hfac]; exact mul_pos (by linarith) hPW
    have : 0 < 2 * A * W + B - S := by
      by_contra hn; push Not at hn
      have := mul_nonpos_of_nonpos_of_nonneg hn h2.le
      linarith
    have : 2 * A * c2 < 2 * A * W := by linarith
    exact lt_of_mul_lt_mul_left this h2A.le
  refine ⟨hαs, hs1, hW0, hWa, hc1W, hc1c2, hc2W, hPhi, fun c hc hc' => ?_, fun c hc hc' => ?_,
    fun c hc => ?_, hlin⟩
  · have h2 := hsign c hc
    have h3 : 2 * A * c < 2 * A * c2 := mul_lt_mul_of_pos_left hc' h2A
    have : 2 * A * c + B - S < 0 := by linarith
    have h4 : (2 * A * c + B - S) * (2 * A * c + B + S) < 0 := mul_neg_of_neg_of_pos this h2
    rw [← hfac] at h4
    by_contra hn; push Not at hn
    exact absurd h4 (not_lt.mpr (mul_nonneg (by linarith : (0:ℝ) ≤ 4 * A) hn))
  · have h2 := hsign c hc
    have h3 : 2 * A * c ≤ 2 * A * c2 := mul_le_mul_of_nonneg_left hc' h2A.le
    have : 2 * A * c + B - S ≤ 0 := by linarith
    have h4 : (2 * A * c + B - S) * (2 * A * c + B + S) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg this h2.le
    rw [← hfac] at h4
    by_contra hn; push Not at hn
    exact absurd h4 (not_le.mpr (mul_pos (by linarith : (0:ℝ) < 4 * A) hn))
  · have h2 := hsign c (by linarith)
    have h3 : 2 * A * c2 < 2 * A * c := mul_lt_mul_of_pos_left hc h2A
    have : 0 < 2 * A * c + B - S := by linarith
    have h4 : 0 < (2 * A * c + B - S) * (2 * A * c + B + S) := mul_pos this h2
    rw [← hfac] at h4
    by_contra hn; push Not at hn
    exact absurd h4 (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ 4 * A) hn))

end PPL1


open YieldPostpone.Payment

namespace PPL1

open PPL3

lemma what_eq (P : Params) (hP : P.Valid) :
    what P * (P.b * (Real.sqrt P.μ - P.α)) = P.a * P.α * Real.sqrt P.μ * (1 - Real.sqrt P.μ) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 ≤ P.μ := by
    rw [hμ]
    have : 0 < 1 - P.θ := by linarith
    positivity
  have hs : Real.sqrt P.μ ^ 2 = P.μ := Real.sq_sqrt hμ0
  unfold what
  set s := Real.sqrt P.μ
  have hαθ : P.b * (P.α + P.θ) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, div_eq_iff hαθ]
  rw [hμ] at hs ⊢
  linear_combination (P.a * P.α * P.b * P.α) * hs

lemma SV_OA (P : Params) (c : ℝ) (σ : Profile) (hQ : ∀ w q, σ.Q w q = q) (w : ℝ) :
    supplierValue P c .OA σ w = (w - c) * σ.q w := by
  simp only [supplierValue, supplierProfit, E, transfer, Scenario.byDelivery, Bool.false_eq_true,
    if_false, hQ]
  ring

/-- the sign of the candidate comparison is the sign of `ŵ - w` -/
lemma cmp_lin (P : Params) (hP : P.Valid) (w : ℝ) :
    (P.a - P.b * (w / P.μ * P.μ / P.α)) - Real.sqrt P.μ * (P.a - P.b * (w / P.μ)) =
      P.b * (Real.sqrt P.μ - P.α) / (P.α * Real.sqrt P.μ) * (what P - w) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ0 : 0 < P.μ := by
    show 0 < P.α * (1 - P.θ) + P.θ
    have : 0 < 1 - P.θ := by linarith
    positivity
  have hs0 : 0 < Real.sqrt P.μ := Real.sqrt_pos.mpr hμ0
  have hs : Real.sqrt P.μ ^ 2 = P.μ := Real.sq_sqrt hμ0.le
  have hW := what_eq P hP
  set s := Real.sqrt P.μ
  have hWv : what P = P.a * P.α * s * (1 - s) / (P.b * (s - P.α)) ∨ s - P.α = 0 := by
    by_cases h : s - P.α = 0
    · right; exact h
    · left; rw [eq_div_iff (by positivity)]; exact hW
  rw [← hs]
  have e1 : w / s ^ 2 * s ^ 2 / P.α = w / P.α := by field_simp
  rw [e1]
  have e2 : P.b * (s - P.α) / (P.α * s) * what P = P.a * (1 - s) := by
    rw [div_mul_eq_mul_div, mul_comm (P.b * (s - P.α)) (what P), hW]
    field_simp
  rw [mul_sub (P.b * (s - P.α) / (P.α * s)), e2]
  field_simp
  ring

/-- Characterization of the supplier's value and the retailer's response in an OA equilibrium. -/
lemma spe_val (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (hσ : IsSPE P c .OA σ) (w : ℝ) (hw : wAdm P c .OA w) :
    (P.a * P.μ ≤ P.b * w ∧ supplierValue P c .OA σ w = 0) ∨
    (P.b * w < P.a * P.μ ∧ w ≤ what P ∧
      σ.q w = (P.a - P.b * (w / P.α)) / (2 * P.α) ∧ σ.p w = (P.a + P.b * (w / P.α)) / (2 * P.b) ∧
      supplierValue P c .OA σ w = (w - c) * ((P.a - P.b * (w / P.α)) / (2 * P.α))) ∨
    (P.b * w < P.a * P.μ ∧ what P ≤ w ∧
      σ.q w = (P.a - P.b * (w / P.μ)) / 2 ∧ σ.p w = (P.a + P.b * (w / P.μ)) / (2 * P.b) ∧
      supplierValue P c .OA σ w = (w - c) * ((P.a - P.b * (w / P.μ)) / 2)) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ0 : 0 < P.μ := by
    show 0 < P.α * (1 - P.θ) + P.θ
    have : 0 < 1 - P.θ := by linarith
    positivity
  have hs0 : 0 < Real.sqrt P.μ := Real.sqrt_pos.mpr hμ0
  have hs : Real.sqrt P.μ ^ 2 = P.μ := Real.sq_sqrt hμ0.le
  obtain ⟨hQ, -, hret, -, -⟩ := (isSPE_OA P c σ).mp hσ
  obtain ⟨hq0, hpA, hopt⟩ := hret w hw
  rw [SV_OA P c σ hQ w]
  obtain ⟨hw1, hw2⟩ := (wAdm_OA P c w).mp hw
  have hw0 : 0 < w := lt_trans hc hw1
  rcases le_or_gt (P.a * P.μ) (P.b * w) with hwa | hwa
  · left
    refine ⟨hwa, ?_⟩
    -- the order must be zero
    have h0 : 0 ≤ retailerProfit P .OA σ w (σ.q w) (σ.p w) := by
      have := hopt 0 (σ.p w) le_rfl hpA
      rw [rp_OA P hP σ w 0 _ le_rfl (hQ w 0)] at this
      obtain ⟨hp0, hpa⟩ := (pAdm_iff P hb _).mp hpA
      have hd : 0 ≤ P.a - P.b * σ.p w := by linarith
      simp only [mul_zero, min_eq_right hd, sub_zero, add_zero] at this
      linarith
    have hq : σ.q w = 0 := by
      by_contra hne
      have hqpos : 0 < σ.q w := lt_of_le_of_ne hq0 (Ne.symm hne)
      obtain ⟨hp0, hpa⟩ := (pAdm_iff P hb _).mp hpA
      rw [rp_OA P hP σ w _ _ hq0 (hQ w _)] at h0
      have h1 : min (P.a - P.b * σ.p w) (σ.q w) ≤ σ.q w := min_le_right _ _
      have h2 : min (P.a - P.b * σ.p w) (P.α * σ.q w) ≤ P.α * σ.q w := min_le_right _ _
      have h3 : P.θ * (σ.p w * min (P.a - P.b * σ.p w) (σ.q w)) ≤ P.θ * (σ.p w * σ.q w) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hp0.le) hθ0.le
      have h4 : (1 - P.θ) * (σ.p w * min (P.a - P.b * σ.p w) (P.α * σ.q w)) ≤
          (1 - P.θ) * (σ.p w * (P.α * σ.q w)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hp0.le) (by linarith)
      have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
      have h6 : P.μ * σ.p w < w := by
        have : P.μ * (P.b * σ.p w) < P.μ * P.a := mul_lt_mul_of_pos_left hpa hμ0
        by_contra h; push Not at h
        have := mul_le_mul_of_nonneg_left h hb.le
        nlinarith
      have h7 : (P.μ * σ.p w - w) * σ.q w < 0 := mul_neg_of_neg_of_pos (by linarith) hqpos
      rw [hμ] at h7
      nlinarith
    rw [hq]; ring
  · right
    obtain ⟨hR, hcases⟩ := resp_OA P hP c σ hσ w hw hc hwa
    have hk : w / P.μ * P.μ / P.α = w / P.α := by field_simp
    have hlin := cmp_lin P hP w
    have hcoef : 0 < P.b * (Real.sqrt P.μ - P.α) / (P.α * Real.sqrt P.μ) := by
      have hαs : P.α < Real.sqrt P.μ := by
        have : P.α ^ 2 < P.μ := by
          show P.α ^ 2 < P.α * (1 - P.θ) + P.θ
          nlinarith [mul_pos hθ0 (show 0 < 1 - P.α by linarith)]
        rw [← hs] at this
        nlinarith
      apply div_pos (mul_pos hb (by linarith)) (by positivity)
    have hw1a : 0 < P.a - P.b * (w / P.μ) := by
      rw [mul_div_assoc', sub_pos, div_lt_iff₀ hμ0]; linarith
    rcases hcases with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3, hak⟩
    · -- non-inflated candidate: forces `ŵ ≤ w`
      right
      have hWw : what P ≤ w := by
        by_contra hlt; push Not at hlt
        have hC : Real.sqrt P.μ * (P.a - P.b * (w / P.μ)) < P.a - P.b * (w / P.μ * P.μ / P.α) := by
          have : 0 < P.b * (Real.sqrt P.μ - P.α) / (P.α * Real.sqrt P.μ) * (what P - w) :=
            mul_pos hcoef (by linarith)
          linarith
        rw [if_pos hC] at e3
        have hpos : 0 < Real.sqrt P.μ * (P.a - P.b * (w / P.μ)) := mul_pos hs0 hw1a
        set X := Real.sqrt P.μ * (P.a - P.b * (w / P.μ))
        set Y := P.a - P.b * (w / P.μ * P.μ / P.α)
        have h1 : X * X < Y * Y := mul_self_lt_mul_self hpos.le hC
        have e4 : Y ^ 2 = X ^ 2 := by
          have : X ^ 2 = P.μ * (P.a - P.b * (w / P.μ)) ^ 2 := by
            simp only [X]; rw [mul_pow, hs]
          rw [this]
          have h4b : (4:ℝ) * P.b ≠ 0 := by positivity
          rwa [div_left_inj' h4b] at e3
        nlinarith
      refine ⟨hwa, hWw, e1, e2, by rw [e1]⟩
    · left
      have hWw : w ≤ what P := by
        by_contra hlt; push Not at hlt
        have hC : ¬ (Real.sqrt P.μ * (P.a - P.b * (w / P.μ)) < P.a - P.b * (w / P.μ * P.μ / P.α)) := by
          have : P.b * (Real.sqrt P.μ - P.α) / (P.α * Real.sqrt P.μ) * (what P - w) < 0 :=
            mul_neg_of_pos_of_neg hcoef (by linarith)
          linarith
        rw [if_neg hC] at e3
        have hpos : 0 < Real.sqrt P.μ * (P.a - P.b * (w / P.μ)) := mul_pos hs0 hw1a
        set X := Real.sqrt P.μ * (P.a - P.b * (w / P.μ))
        set Y := P.a - P.b * (w / P.μ * P.μ / P.α)
        have e4 : (Y - X) * (Y + X) = 0 := by
          have : X ^ 2 = P.μ * (P.a - P.b * (w / P.μ)) ^ 2 := by
            simp only [X]; rw [mul_pow, hs]
          have h4b : (4:ℝ) * P.b ≠ 0 := by positivity
          have e5 : Y ^ 2 = X ^ 2 := by
            rw [this]; rw [div_left_inj' h4b] at e3; exact e3.symm
          linear_combination e5
        have hYX : Y = X := by
          rcases mul_eq_zero.mp e4 with h | h
          · linarith
          · linarith
        have : P.b * (Real.sqrt P.μ - P.α) / (P.α * Real.sqrt P.μ) * (what P - w) = 0 := by
          rw [← hlin]; simp only [X, Y] at hYX; linarith
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · linarith
      rw [hk] at e1 e2
      refine ⟨hwa, hWw, e1, e2, by rw [e1]⟩

end PPL1


open YieldPostpone.Payment

namespace PPL1

open PPL3

/-- the comparison quadratic `Φ(c) = α²(aμ - bc)² - 4bμ(aα - bŵ)(ŵ - c)` -/
noncomputable def Phi (P : Params) (c : ℝ) : ℝ :=
  P.α ^ 2 * (P.a * P.μ - P.b * c) ^ 2 - 4 * P.b * P.μ * (P.a * P.α - P.b * what P) * (what P - c)

lemma thrOA (P : Params) (hP : P.Valid) :
    0 < what P ∧ P.b * what P < P.a * P.α ∧ cOA1 P < what P ∧ cOA1 P < cOA2 P ∧
    cOA2 P < what P ∧
    (∀ c, cOA1 P ≤ c → c < cOA2 P → Phi P c < 0) ∧
    (∀ c, cOA1 P ≤ c → c ≤ cOA2 P → Phi P c ≤ 0) ∧
    (∀ c, cOA2 P < c → 0 < Phi P c) ∧
    (∀ c, Real.sqrt P.μ * (P.a * P.α - P.b * c) - P.α * (P.a * P.μ - P.b * c) =
      (what P - c) * (P.b * (Real.sqrt P.μ - P.α))) ∧
    P.α < Real.sqrt P.μ ∧
    P.b * cOA1 P = 2 * P.b * what P - P.a * P.α := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < P.μ := by rw [hμ]; have : 0 < 1 - P.θ := by linarith
                           positivity
  have hs0 : 0 < Real.sqrt P.μ := Real.sqrt_pos.mpr hμ0
  have hs2 : Real.sqrt P.μ ^ 2 = P.μ := Real.sq_sqrt hμ0.le
  have hs : Real.sqrt P.μ ^ 2 = P.α * (1 - P.θ) + P.θ := by rw [hs2]; rfl
  have h := phi_facts P.a P.b P.α P.θ (Real.sqrt P.μ) (what P) ha hb hα0 hα1 hθ0 hθ1 hs0 hs
    (what_eq P hP)
  dsimp only at h
  simp only [hs2] at h
  obtain ⟨hαs, -, hW0, hWa, hc1W, hc1c2, hc2W, hPhi, hneg, hle, hpos, hlin⟩ := h
  have hc1 : cOA1 P = 2 * what P - P.a * P.α / P.b := by
    unfold cOA1 what
    have : P.b * (P.α + P.θ) ≠ 0 := by positivity
    field_simp
    rw [hμ]; ring
  have hc2 : cOA2 P = (-(-(2 * P.α ^ 2 * P.a * P.μ * P.b) +
      4 * P.b * P.μ * (P.a * P.α - P.b * what P)) +
      Real.sqrt ((-(2 * P.α ^ 2 * P.a * P.μ * P.b) + 4 * P.b * P.μ * (P.a * P.α - P.b * what P)) ^ 2 -
        4 * (P.α ^ 2 * P.b ^ 2) * (P.α ^ 2 * (P.a * P.μ) ^ 2 -
          4 * P.b * P.μ * (P.a * P.α - P.b * what P) * what P))) / (2 * (P.α ^ 2 * P.b ^ 2)) := rfl
  have hPhi' : ∀ c, Phi P c = P.α ^ 2 * P.b ^ 2 * c ^ 2 +
      (-(2 * P.α ^ 2 * P.a * P.μ * P.b) + 4 * P.b * P.μ * (P.a * P.α - P.b * what P)) * c +
      (P.α ^ 2 * (P.a * P.μ) ^ 2 - 4 * P.b * P.μ * (P.a * P.α - P.b * what P) * what P) := by
    intro c; unfold Phi; rw [hPhi]
  rw [← hc1] at hc1W hc1c2 hneg hle
  rw [← hc2] at hc1c2 hc2W hneg hle hpos
  refine ⟨hW0, hWa, hc1W, hc1c2, hc2W, fun c h1 h2 => ?_, fun c h1 h2 => ?_, fun c h1 => ?_,
    hlin, hαs, ?_⟩
  · rw [hPhi']; exact hneg c h1 h2
  · rw [hPhi']; exact hle c h1 h2
  · rw [hPhi']; exact hpos c h1
  · rw [hc1]; field_simp

lemma G1_gap (a b α c w : ℝ) (hb : 0 < b) (hα : 0 < α) :
    (w - c) * ((a - b * (w / α)) / (2 * α)) =
      (a * α - b * c) ^ 2 / (8 * b * α ^ 2) - b / (2 * α ^ 2) * (w - (a * α + b * c) / (2 * b)) ^ 2 := by
  field_simp; ring

lemma G1_mono (a b α c w W : ℝ) (hα : 0 < α) :
    (W - c) * ((a - b * (W / α)) / (2 * α)) - (w - c) * ((a - b * (w / α)) / (2 * α)) =
      (W - w) * ((a * α + b * c) - b * (W + w)) / (2 * α ^ 2) := by
  field_simp; ring

lemma G2_gap (a b μ c w : ℝ) (hb : 0 < b) (hμ : 0 < μ) :
    (w - c) * ((a - b * (w / μ)) / 2) =
      (a * μ - b * c) ^ 2 / (8 * b * μ) - b / (2 * μ) * (w - (a * μ + b * c) / (2 * b)) ^ 2 := by
  field_simp; ring

lemma Phi_rel (P : Params) (hP : P.Valid) (c : ℝ) :
    (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * P.μ) -
      (what P - c) * ((P.a - P.b * (what P / P.α)) / (2 * P.α)) =
      Phi P c / (8 * P.b * P.μ * P.α ^ 2) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hμ0 : 0 < P.μ := by
    show 0 < P.α * (1 - P.θ) + P.θ
    have : 0 < 1 - P.θ := by linarith
    positivity
  unfold Phi
  field_simp
  ring

/-- outcome for the inflated candidate at the equilibrium wholesale price -/
lemma out_cand2 (P : Params) (hP : P.Valid) (c : ℝ) (σ : Profile) (hQ : ∀ w q, σ.Q w q = q)
    (hq : σ.q σ.w = (P.a - P.b * (σ.w / P.α)) / (2 * P.α))
    (hp : σ.p σ.w = (P.a + P.b * (σ.w / P.α)) / (2 * P.b))
    (hpos : 0 < P.a - P.b * (σ.w / P.α)) :
    piR P c .OA σ = ((P.a - P.b * (σ.w / P.α)) / 2) ^ 2 / P.b ∧
    CS P c .OA σ = ((P.a - P.b * (σ.w / P.α)) / 2) ^ 2 / (2 * P.b) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hq0 : 0 ≤ σ.q σ.w := by rw [hq]; positivity
  set d := (P.a - P.b * (σ.w / P.α)) / 2 with hd
  have hdp : P.a - P.b * σ.p σ.w = d := by rw [hp, hd]; field_simp; ring
  have hqd : σ.q σ.w = d / P.α := by rw [hq, hd]; field_simp
  have hd0 : 0 < d := by rw [hd]; linarith
  have hdq : d ≤ d / P.α := by rw [le_div_iff₀ hα0]; nlinarith
  have hαq : P.α * (d / P.α) = d := by field_simp
  constructor
  · show retailerProfit P .OA σ σ.w (σ.q σ.w) (σ.p σ.w) = _
    rw [rp_OA P hP σ σ.w _ _ hq0 (hQ _ _), hdp, hqd, hαq, min_self, min_eq_left hdq, hp, hd]
    field_simp
    ring
  · rw [CS_OA P hP c σ hQ hq0, surplus_eq P hb, surplus_eq P hb, hdp, hqd, hαq, min_self,
      min_eq_left hdq, hp, hd]
    field_simp
    ring

/-- outcome for the non-inflated candidate at the equilibrium wholesale price -/
lemma out_cand1 (P : Params) (hP : P.Valid) (c : ℝ) (σ : Profile) (hQ : ∀ w q, σ.Q w q = q)
    (hq : σ.q σ.w = (P.a - P.b * (σ.w / P.μ)) / 2)
    (hp : σ.p σ.w = (P.a + P.b * (σ.w / P.μ)) / (2 * P.b))
    (hpos : 0 < P.a - P.b * (σ.w / P.μ)) :
    piR P c .OA σ = P.μ * ((P.a - P.b * (σ.w / P.μ)) / 2) ^ 2 / P.b ∧
    CS P c .OA σ = (P.α * (2 - P.α) * (1 - P.θ) + P.θ) *
      ((P.a - P.b * (σ.w / P.μ)) / 2) ^ 2 / (2 * P.b) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < P.μ := by
    rw [hμ]; have : 0 < 1 - P.θ := by linarith
    positivity
  have hq0 : 0 ≤ σ.q σ.w := by rw [hq]; linarith
  set d := (P.a - P.b * (σ.w / P.μ)) / 2 with hd
  have hdp : P.a - P.b * σ.p σ.w = d := by rw [hp, hd]; field_simp; ring
  have hd0 : 0 < d := by rw [hd]; linarith
  have hαd : P.α * d ≤ d := by nlinarith
  constructor
  · show retailerProfit P .OA σ σ.w (σ.q σ.w) (σ.p σ.w) = _
    rw [rp_OA P hP σ σ.w _ _ hq0 (hQ _ _), hdp, hq, min_self, min_eq_right hαd, hp]
    have e : σ.w = P.μ * (P.a / P.b - 2 * d / P.b) := by rw [hd]; field_simp; ring
    rw [e]
    field_simp
    rw [hμ]
    ring
  · rw [CS_OA P hP c σ hQ hq0, surplus_eq P hb, surplus_eq P hb, hdp, hq, min_self,
      min_eq_right hαd, hp]
    have e : σ.w = P.μ * (P.a / P.b - 2 * d / P.b) := by rw [hd]; field_simp; ring
    rw [e]
    field_simp
    ring

end PPL1


open YieldPostpone.Payment

namespace PPL1

open PPL3

/-- the retailer's order in the explicit OA equilibrium -/
noncomputable def qO (P : Params) (w : ℝ) : ℝ :=
  if w ≤ what P then (P.a - P.b * (w / P.α)) / (2 * P.α)
  else if P.b * w < P.a * P.μ then (P.a - P.b * (w / P.μ)) / 2 else 0

/-- the retailer's (ex ante) price in the explicit OA equilibrium -/
noncomputable def pO (P : Params) (w : ℝ) : ℝ :=
  if w ≤ what P then (P.a + P.b * (w / P.α)) / (2 * P.b)
  else if P.b * w < P.a * P.μ then (P.a + P.b * (w / P.μ)) / (2 * P.b) else P.a / (2 * P.b)

noncomputable def σO (P : Params) (ws : ℝ) : Profile :=
  ⟨ws, fun _ q => q, qO P, pO P, fun _ _ _ => 0⟩

lemma retO (P : Params) (hP : P.Valid) (c ws : ℝ) (hc : 0 < c) (w : ℝ) (hw : wAdm P c .OA w) :
    0 ≤ qO P w ∧ pAdm P (pO P w) ∧
    ∀ q' p', 0 ≤ q' → pAdm P p' →
      retailerProfit P .OA (σO P ws) w q' p' ≤ retailerProfit P .OA (σO P ws) w (qO P w) (pO P w) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < P.μ := by
    rw [hμ]; have : 0 < 1 - P.θ := by linarith
    positivity
  have hs0 : 0 < Real.sqrt P.μ := Real.sqrt_pos.mpr hμ0
  have hs : Real.sqrt P.μ ^ 2 = P.μ := Real.sq_sqrt hμ0.le
  obtain ⟨hW0, hWa, -, -, -, -, -, -, -, hαs, -⟩ := thrOA P hP
  obtain ⟨hw1, hw2⟩ := (wAdm_OA P c w).mp hw
  have hw0 : 0 < w := lt_trans hc hw1
  have hQ : ∀ w q, (σO P ws).Q w q = q := fun _ _ => rfl
  have hRP : ∀ q p, 0 ≤ q → retailerProfit P .OA (σO P ws) w q p =
      P.θ * (p * min (P.a - P.b * p) q - w / P.μ * q) +
        (1 - P.θ) * (p * min (P.a - P.b * p) (P.α * q) - w / P.μ * (P.α * q)) := by
    intro q p hq
    rw [rp_OA P hP _ w q p hq (hQ w q)]
    exact rp_RL P.θ P.α P.μ w p q _ _ hμ hμ0
  have hlin := cmp_lin P hP w
  have hk : w / P.μ * P.μ / P.α = w / P.α := by field_simp
  rw [hk] at hlin
  have hcoef : 0 < P.b * (Real.sqrt P.μ - P.α) / (P.α * Real.sqrt P.μ) :=
    div_pos (mul_pos hb (by linarith)) (by positivity)
  have hX : ∀ (_ : P.b * w < P.a * P.μ), 0 < Real.sqrt P.μ * (P.a - P.b * (w / P.μ)) := by
    intro hwa
    have : P.b * (w / P.μ) < P.a := by rw [mul_div_assoc', div_lt_iff₀ hμ0]; linarith
    have : 0 < P.a - P.b * (w / P.μ) := by linarith
    positivity
  unfold qO pO
  split_ifs with h1 h2
  · -- inflated candidate
    have hwa : P.b * w < P.a * P.μ := by
      have : P.b * w ≤ P.b * what P := mul_le_mul_of_nonneg_left h1 hb.le
      have : P.a * P.α < P.a * P.μ := by
        apply mul_lt_mul_of_pos_left _ ha
        rw [← hs]; nlinarith
      linarith
    have hw1a : P.b * (w / P.μ) < P.a := by rw [mul_div_assoc', div_lt_iff₀ hμ0]; linarith
    have hXp := hX hwa
    have hYX : Real.sqrt P.μ * (P.a - P.b * (w / P.μ)) ≤ P.a - P.b * (w / P.α) := by
      have : 0 ≤ P.b * (Real.sqrt P.μ - P.α) / (P.α * Real.sqrt P.μ) * (what P - w) :=
        mul_nonneg hcoef.le (by linarith)
      linarith
    have hak : 0 < P.a - P.b * (w / P.α) := lt_of_lt_of_le hXp hYX
    refine ⟨by positivity, ?_, fun q' p' hq' hp' => ?_⟩
    · rw [pAdm_iff P hb]
      refine ⟨by positivity, ?_⟩
      have : P.b * ((P.a + P.b * (w / P.α)) / (2 * P.b)) = (P.a + P.b * (w / P.α)) / 2 := by
        field_simp
      rw [this]; linarith
    · have hq2 : 0 ≤ (P.a - P.b * (w / P.α)) / (2 * P.α) := by positivity
      rw [hRP _ _ hq', hRP _ _ hq2, ← hk]
      rw [← hk] at hak hYX
      obtain ⟨hp0, hpa⟩ := (pAdm_iff P hb p').mp hp'
      obtain ⟨hle, -⟩ := RL_le P.a P.b P.α P.θ P.μ (Real.sqrt P.μ) (w / P.μ) q' p'
        (w / P.μ * P.μ / P.α)
        (if Real.sqrt P.μ * (P.a - P.b * (w / P.μ)) < P.a - P.b * (w / P.μ * P.μ / P.α) then
          (P.a - P.b * (w / P.μ * P.μ / P.α)) ^ 2 / (4 * P.b)
         else P.μ * (P.a - P.b * (w / P.μ)) ^ 2 / (4 * P.b))
        hb hα0 hα1 hθ0 hθ1 hμ hs0 hs (div_pos hw0 hμ0) hw1a hq' hp0 hpa rfl rfl
      rw [cand2_val P.a P.b P.α P.θ P.μ (w / P.μ) _ hb hα0 hα1 hμ rfl hak]
      refine le_trans hle ?_
      split_ifs with hC
      · exact le_rfl
      · have heq : P.a - P.b * (w / P.μ * P.μ / P.α) = Real.sqrt P.μ * (P.a - P.b * (w / P.μ)) := by
          push Not at hC; linarith
        rw [heq, mul_pow, hs]
  · -- non-inflated candidate
    push Not at h1
    have hw1a : P.b * (w / P.μ) < P.a := by rw [mul_div_assoc', div_lt_iff₀ hμ0]; linarith
    have hXp := hX h2
    have hYX : P.a - P.b * (w / P.α) < Real.sqrt P.μ * (P.a - P.b * (w / P.μ)) := by
      have : P.b * (Real.sqrt P.μ - P.α) / (P.α * Real.sqrt P.μ) * (what P - w) < 0 :=
        mul_neg_of_pos_of_neg hcoef (by linarith)
      linarith
    refine ⟨by linarith, ?_, fun q' p' hq' hp' => ?_⟩
    · rw [pAdm_iff P hb]
      refine ⟨by positivity, ?_⟩
      have : P.b * ((P.a + P.b * (w / P.μ)) / (2 * P.b)) = (P.a + P.b * (w / P.μ)) / 2 := by
        field_simp
      rw [this]; linarith
    · have hq1 : 0 ≤ (P.a - P.b * (w / P.μ)) / 2 := by linarith
      rw [hRP _ _ hq', hRP _ _ hq1]
      rw [← hk] at hYX
      obtain ⟨hp0, hpa⟩ := (pAdm_iff P hb p').mp hp'
      obtain ⟨hle, -⟩ := RL_le P.a P.b P.α P.θ P.μ (Real.sqrt P.μ) (w / P.μ) q' p'
        (w / P.μ * P.μ / P.α)
        (if Real.sqrt P.μ * (P.a - P.b * (w / P.μ)) < P.a - P.b * (w / P.μ * P.μ / P.α) then
          (P.a - P.b * (w / P.μ * P.μ / P.α)) ^ 2 / (4 * P.b)
         else P.μ * (P.a - P.b * (w / P.μ)) ^ 2 / (4 * P.b))
        hb hα0 hα1 hθ0 hθ1 hμ hs0 hs (div_pos hw0 hμ0) hw1a hq' hp0 hpa rfl rfl
      rw [cand1_val P.a P.b P.α P.θ P.μ (w / P.μ) hb hα0 hα1 hμ hw1a]
      rw [if_neg (not_lt.mpr hYX.le)] at hle
      exact hle
  · -- no order
    push Not at h1 h2
    refine ⟨le_rfl, ?_, fun q' p' hq' hp' => ?_⟩
    · rw [pAdm_iff P hb]
      refine ⟨by positivity, ?_⟩
      have : P.b * (P.a / (2 * P.b)) = P.a / 2 := by field_simp
      rw [this]; linarith
    · have h0 : retailerProfit P .OA (σO P ws) w 0 (P.a / (2 * P.b)) = 0 := by
        rw [rp_OA P hP _ w 0 _ le_rfl (hQ w 0)]
        have hd : 0 ≤ P.a - P.b * (P.a / (2 * P.b)) := by
          have : P.b * (P.a / (2 * P.b)) = P.a / 2 := by field_simp
          rw [this]; linarith
        simp only [mul_zero, min_eq_right hd, sub_zero, add_zero]
      rw [h0]
      exact rp_nonpos P hP _ w q' p' hq' (hQ w q') hp' h2

end PPL1


open YieldPostpone.Payment

namespace PPL1

open PPL3

/-- the supplier's value in the explicit profile -/
lemma SV_O (P : Params) (c ws w : ℝ) :
    supplierValue P c .OA (σO P ws) w = (w - c) * qO P w :=
  SV_OA P c (σO P ws) (fun _ _ => rfl) w

lemma spe_O (P : Params) (hP : P.Valid) (c ws : ℝ) (hc : 0 < c) (hws : wAdm P c .OA ws)
    (hmax : ∀ w, wAdm P c .OA w → (w - c) * qO P w ≤ (ws - c) * qO P ws) :
    IsSPE P c .OA (σO P ws) := by
  refine (isSPE_OA P c _).mpr ⟨fun _ _ => rfl, trivial, fun w hw => retO P hP c ws hc w hw, hws,
    fun w hw => ?_⟩
  show supplierValue P c .OA (σO P ws) w ≤ supplierValue P c .OA (σO P ws) ws
  rw [SV_O, SV_O]
  exact hmax w hw

/-- the low-price branch can be approached from the left -/
lemma approach (a b α c W v : ℝ) (ha : 0 < a) (hb : 0 < b) (hα : 0 < α) (hc : 0 < c) (hcW : c < W)
    (hv : v < (W - c) * ((a - b * (W / α)) / (2 * α))) :
    ∃ w, c < w ∧ w < W ∧ v < (w - c) * ((a - b * (w / α)) / (2 * α)) := by
  set G := (W - c) * ((a - b * (W / α)) / (2 * α))
  set K := (a * α + b * c) / (2 * α ^ 2) with hK
  have hK0 : 0 < K := by positivity
  set δ := min ((W - c) / 2) ((G - v) / (2 * K)) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (div_pos (by linarith) (by positivity))
  have hδ1 : δ ≤ (W - c) / 2 := min_le_left _ _
  have hδ2 : δ ≤ (G - v) / (2 * K) := min_le_right _ _
  refine ⟨W - δ, by linarith, by linarith, ?_⟩
  have hm := G1_mono a b α c (W - δ) W hα
  have hb0 : 0 ≤ b * (W + (W - δ)) := by
    have : 0 < W := by linarith
    have : 0 < W - δ := by linarith
    positivity
  have h1 : G - (W - δ - c) * ((a - b * ((W - δ) / α)) / (2 * α)) ≤ δ * K := by
    rw [hm]
    have e : (W - (W - δ)) * (a * α + b * c - b * (W + (W - δ))) / (2 * α ^ 2) =
        δ * K - δ * (b * (W + (W - δ))) / (2 * α ^ 2) := by
      rw [hK]; field_simp; ring
    rw [e]
    have : 0 ≤ δ * (b * (W + (W - δ))) / (2 * α ^ 2) := by positivity
    linarith
  have h2 : δ * K ≤ (G - v) / 2 := by
    have := mul_le_mul_of_nonneg_right hδ2 hK0.le
    have e : (G - v) / (2 * K) * K = (G - v) / 2 := by field_simp
    linarith
  linarith

end PPL1

open PPL1 PPL3

set_option maxHeartbeats 4000000 in
theorem solution (P : Params) (hP : P.Valid) :
    cOA1 P < cOA2 P ∧ cOA2 P < P.a * P.μ / P.b ∧
    ∀ c, costAdm P c →
      (∃ σ : Profile, IsSPE P c .OA σ) ∧
      (∀ σ : Profile, IsSPE P c .OA σ →
        (c < max 0 (cOA1 P) → outcome P c .OA σ = OA1 P c) ∧
        (max 0 (cOA1 P) < c ∧ c < max 0 (cOA2 P) →
          outcome P c .OA σ =
            ((P.a * P.α - P.b * what P) ^ 2 / (4 * P.b * P.α ^ 2),
             (P.a * P.α - P.b * what P) * (what P - c) / (2 * P.α ^ 2),
             (P.a * P.α - P.b * what P) ^ 2 / (8 * P.b * P.α ^ 2))) ∧
        (max 0 (cOA2 P) < c → outcome P c .OA σ = OA3 P c)) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < P.μ := by
    rw [hμ]; have : 0 < 1 - P.θ := by linarith
    positivity
  have hs0 : 0 < Real.sqrt P.μ := Real.sqrt_pos.mpr hμ0
  have hs : Real.sqrt P.μ ^ 2 = P.μ := Real.sq_sqrt hμ0.le
  obtain ⟨hW0, hWa, hc1W, hc1c2, hc2W, hneg, hle, hpos, hlin, hαs, hbc1⟩ := thrOA P hP
  have hαμ : P.α < P.μ := by rw [← hs]; nlinarith
  have hWμ : P.b * what P < P.a * P.μ := by
    have : P.a * P.α < P.a * P.μ := mul_lt_mul_of_pos_left hαμ ha
    linarith
  have hμ1 : P.μ < 1 := by rw [hμ]; nlinarith [mul_pos (show 0 < 1 - P.θ by linarith) (show 0 < 1 - P.α by linarith)]
  refine ⟨hc1c2, ?_, fun c hc => ?_⟩
  · rw [lt_div_iff₀ hb, mul_comm]
    have : P.b * cOA2 P < P.b * what P := mul_lt_mul_of_pos_left hc2W hb
    linarith
  obtain ⟨hc0, hcμ'⟩ := hc
  have hcμ : P.b * c < P.a * P.μ := by rw [lt_div_iff₀ hb] at hcμ'; linarith
  set W := what P with hWdef
  have hPrel := Phi_rel P hP c
  rw [← hWdef] at hPrel
  -- g1* > g2* whenever c < ŵ
  have hg12 : c < W → (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * P.μ) <
      (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) := by
    intro hcW
    have h1 := hlin c
    have h2 : 0 < (W - c) * (P.b * (Real.sqrt P.μ - P.α)) := mul_pos (by linarith)
      (mul_pos hb (by linarith))
    have h3 : 0 < P.α * (P.a * P.μ - P.b * c) := mul_pos hα0 (by linarith)
    have h4 : (P.α * (P.a * P.μ - P.b * c)) ^ 2 < (Real.sqrt P.μ * (P.a * P.α - P.b * c)) ^ 2 := by
      apply pow_lt_pow_left₀ (by linarith) h3.le (by norm_num)
    rw [mul_pow, mul_pow, hs] at h4
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have := mul_lt_mul_of_pos_left h4 (by positivity : (0:ℝ) < 8 * P.b)
    nlinarith
  have hG1pos : c < W → 0 < (W - c) * ((P.a - P.b * (W / P.α)) / (2 * P.α)) := by
    intro hcW
    have : P.b * (W / P.α) < P.a := by
      rw [mul_div_assoc', div_lt_iff₀ hα0]; linarith
    have : 0 < P.a - P.b * (W / P.α) := by linarith
    have : 0 < W - c := by linarith
    positivity
  have hmono : cOA1 P ≤ c → ∀ w, w ≤ W →
      (w - c) * ((P.a - P.b * (w / P.α)) / (2 * P.α)) ≤
        (W - c) * ((P.a - P.b * (W / P.α)) / (2 * P.α)) ∧
      (w < W → (w - c) * ((P.a - P.b * (w / P.α)) / (2 * P.α)) <
        (W - c) * ((P.a - P.b * (W / P.α)) / (2 * P.α))) := by
    intro hc1 w hw
    have hm := G1_mono P.a P.b P.α c w W hα0
    have hbc : 2 * P.b * W - P.a * P.α ≤ P.b * c := by
      rw [← hbc1]; exact mul_le_mul_of_nonneg_left hc1 hb.le
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
  -- explicit thresholds and prices
  have hc1lt : ∀ (_ : c < cOA1 P), P.a * P.α + P.b * c < 2 * P.b * W := by
    intro h; have := mul_lt_mul_of_pos_left h hb; linarith
  have hG1g : ∀ w, (w - c) * ((P.a - P.b * (w / P.α)) / (2 * P.α)) =
      (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) -
        P.b / (2 * P.α ^ 2) * (w - (P.a * P.α + P.b * c) / (2 * P.b)) ^ 2 :=
    fun w => G1_gap P.a P.b P.α c w hb hα0
  have hG2g : ∀ w, (w - c) * ((P.a - P.b * (w / P.μ)) / 2) =
      (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * P.μ) -
        P.b / (2 * P.μ) * (w - (P.a * P.μ + P.b * c) / (2 * P.b)) ^ 2 :=
    fun w => G2_gap P.a P.b P.μ c w hb hμ0
  have hG1le : ∀ w, (w - c) * ((P.a - P.b * (w / P.α)) / (2 * P.α)) ≤
      (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) := by
    intro w; rw [hG1g]
    have : 0 ≤ P.b / (2 * P.α ^ 2) * (w - (P.a * P.α + P.b * c) / (2 * P.b)) ^ 2 := by positivity
    linarith
  have hG2le : ∀ w, (w - c) * ((P.a - P.b * (w / P.μ)) / 2) ≤
      (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * P.μ) := by
    intro w; rw [hG2g]
    have : 0 ≤ P.b / (2 * P.μ) * (w - (P.a * P.μ + P.b * c) / (2 * P.b)) ^ 2 := by positivity
    linarith
  have hden : 0 < 8 * P.b * P.μ * P.α ^ 2 := by positivity
  have hg2pos : 0 < (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * P.μ) := by
    have : 0 < P.a * P.μ - P.b * c := by linarith
    positivity
  have hwAdm : ∀ w, c < w → P.b * w < P.a → wAdm P c .OA w := by
    intro w h1 h2
    rw [wAdm_OA]; exact ⟨h1, by rw [lt_div_iff₀ hb]; linarith⟩
  set w1 := (P.a * P.α + P.b * c) / (2 * P.b) with hw1
  set w2 := (P.a * P.μ + P.b * c) / (2 * P.b) with hw2
  have hbw1 : P.b * w1 = (P.a * P.α + P.b * c) / 2 := by rw [hw1]; field_simp
  have hbw2 : P.b * w2 = (P.a * P.μ + P.b * c) / 2 := by rw [hw2]; field_simp
  have hcW1 : c < cOA1 P → w1 < W := by
    intro h
    have := hc1lt h
    have : P.b * w1 < P.b * W := by rw [hbw1]; linarith
    exact lt_of_mul_lt_mul_left this hb.le
  have hW2 : cOA1 P ≤ c → W < w2 := by
    intro h
    have hbc : 2 * P.b * W - P.a * P.α ≤ P.b * c := by
      rw [← hbc1]; exact mul_le_mul_of_nonneg_left h hb.le
    have : P.b * W < P.b * w2 := by
      rw [hbw2]
      have : P.a * P.α < P.a * P.μ := mul_lt_mul_of_pos_left hαμ ha
      linarith
    exact lt_of_mul_lt_mul_left this hb.le
  have hW1a : P.b * W < P.a := by
    have : P.a * P.α < P.a := by nlinarith
    linarith
  -- existence
  constructor
  · by_cases hA : c < cOA1 P
    · have hw1W := hcW1 hA
      have hca : P.b * c < P.a * P.α := by
        have : P.b * c < P.b * W := by
          have := lt_trans hA hc1W; exact mul_lt_mul_of_pos_left this hb
        linarith
      have hadm : wAdm P c .OA w1 := hwAdm w1 (by
          have : P.b * c < P.b * w1 := by rw [hbw1]; linarith
          exact lt_of_mul_lt_mul_left this hb.le) (by rw [hbw1]; nlinarith)
      refine ⟨_, spe_O P hP c w1 hc0 hadm (fun w hw => ?_)⟩
      have hv1 : (w1 - c) * qO P w1 = (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) := by
        unfold qO; rw [if_pos hw1W.le, hG1g, hw1]; ring
      rw [hv1]
      unfold qO
      split_ifs with h1 h2
      · exact hG1le w
      · exact le_trans (hG2le w) (hg12 (lt_trans hA hc1W)).le
      · rw [mul_zero]; positivity
    · push Not at hA
      by_cases hB : c ≤ cOA2 P
      · have hcW : c < W := lt_of_le_of_lt hB hc2W
        have hadm : wAdm P c .OA W := hwAdm W hcW hW1a
        refine ⟨_, spe_O P hP c W hc0 hadm (fun w hw => ?_)⟩
        have hvW : (W - c) * qO P W = (W - c) * ((P.a - P.b * (W / P.α)) / (2 * P.α)) := by
          unfold qO; rw [if_pos le_rfl]
        rw [hvW]
        unfold qO
        split_ifs with h1 h2
        · exact (hmono hA w h1).1
        · have h3 := hle c hA hB
          have : (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * P.μ) -
              (W - c) * ((P.a - P.b * (W / P.α)) / (2 * P.α)) ≤ 0 := by
            rw [hPrel]; exact div_nonpos_of_nonpos_of_nonneg h3 hden.le
          linarith [hG2le w]
        · rw [mul_zero]; exact (hG1pos hcW).le
      · push Not at hB
        have hW2' := hW2 hA
        have hadm : wAdm P c .OA w2 := hwAdm w2 (by
            have : P.b * c < P.b * w2 := by rw [hbw2]; linarith
            exact lt_of_mul_lt_mul_left this hb.le) (by rw [hbw2]; nlinarith)
        refine ⟨_, spe_O P hP c w2 hc0 hadm (fun w hw => ?_)⟩
        have hv2 : (w2 - c) * qO P w2 = (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * P.μ) := by
          unfold qO
          rw [if_neg (not_le.mpr hW2'), if_pos (by rw [hbw2]; linarith), hG2g, hw2]; ring
        rw [hv2]
        unfold qO
        split_ifs with h1 h2
        · have h3 := hpos c hB
          have : 0 < (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * P.μ) -
              (W - c) * ((P.a - P.b * (W / P.α)) / (2 * P.α)) := by
            rw [hPrel]; exact div_pos h3 hden
          linarith [(hmono hA w h1).1]
        · exact hG2le w
        · rw [mul_zero]; exact hg2pos.le
  -- uniqueness
  intro σ hσ
  obtain ⟨hQ, -, -, hwσ, hopt⟩ := (isSPE_OA P c σ).mp hσ
  have hV := fun w hw => spe_val P hP c hc0 σ hσ w hw
  have hpiS : piS P c .OA σ = supplierValue P c .OA σ σ.w := rfl
  refine ⟨fun hA => ?_, fun ⟨hB1, hB2⟩ => ?_, fun hC => ?_⟩
  · -- low cost: the inflated optimum `w₁`
    have hA' : c < cOA1 P := by
      rcases le_total 0 (cOA1 P) with h | h
      · rwa [max_eq_right h] at hA
      · rw [max_eq_left h] at hA; linarith
    have hw1W := hcW1 hA'
    have hca : P.b * c < P.a * P.α := by
      have : P.b * c < P.b * W := by
        have := lt_trans hA' hc1W; exact mul_lt_mul_of_pos_left this hb
      linarith
    have hadm : wAdm P c .OA w1 := hwAdm w1 (by
        have : P.b * c < P.b * w1 := by rw [hbw1]; linarith
        exact lt_of_mul_lt_mul_left this hb.le) (by rw [hbw1]; nlinarith)
    have hg1pos : 0 < (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) := by
      have : 0 < P.a * P.α - P.b * c := by linarith
      positivity
    have hVw1 : supplierValue P c .OA σ w1 = (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) := by
      rcases hV w1 hadm with ⟨h, -⟩ | ⟨-, -, -, -, h⟩ | ⟨-, h, -⟩
      · exfalso; rw [hbw1] at h; nlinarith
      · rw [h, hG1g, hw1]; ring
      · exfalso; linarith
    have hge := hopt w1 hadm
    rw [hVw1] at hge
    rcases hV σ.w hwσ with ⟨-, h⟩ | ⟨hwa, -, hq, hp, h⟩ | ⟨-, -, -, -, h⟩
    · linarith
    · rw [h, hG1g] at hge
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
      have hpos : 0 < P.a - P.b * (σ.w / P.α) := by
        rw [hws, mul_div_assoc', sub_pos, div_lt_iff₀ hα0, hbw1]; linarith
      obtain ⟨e1, e3⟩ := out_cand2 P hP c σ hQ hq hp hpos
      have e2 : piS P c .OA σ = (σ.w - c) * ((P.a - P.b * (σ.w / P.α)) / (2 * P.α)) := by
        rw [hpiS, h]
      unfold outcome OA1
      rw [e1, e2, e3, hws, hw1]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> field_simp <;> ring
    · rw [h] at hge
      linarith [hG2le σ.w, hg12 (lt_trans hA' hc1W)]
  · -- middle cost: the kink price `ŵ` with the inflated response
    have hc1 : cOA1 P < c := lt_of_le_of_lt (le_max_right _ _) hB1
    have hc2 : c < cOA2 P := by
      rcases le_total 0 (cOA2 P) with h | h
      · rwa [max_eq_right h] at hB2
      · rw [max_eq_left h] at hB2; linarith
    have hcW : c < W := lt_trans hc2 hc2W
    have hadm : wAdm P c .OA W := hwAdm W hcW hW1a
    have hG1W := hG1pos hcW
    have hgap : (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * P.μ) <
        (W - c) * ((P.a - P.b * (W / P.α)) / (2 * P.α)) := by
      have h3 := hneg c hc1.le hc2
      have : (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * P.μ) -
          (W - c) * ((P.a - P.b * (W / P.α)) / (2 * P.α)) < 0 := by
        rw [hPrel]; exact div_neg_of_neg_of_pos h3 hden
      linarith
    -- the equilibrium value is at least `G₁(ŵ)`
    have hVge : (W - c) * ((P.a - P.b * (W / P.α)) / (2 * P.α)) ≤ supplierValue P c .OA σ σ.w := by
      by_contra hlt; push Not at hlt
      obtain ⟨w, hcw, hwW, hv⟩ := approach P.a P.b P.α c W _ ha hb hα0 hc0 hcW hlt
      have hadmw : wAdm P c .OA w := hwAdm w hcw (by
        have : P.b * w < P.b * W := mul_lt_mul_of_pos_left hwW hb
        linarith)
      have h1 := hopt w hadmw
      rcases hV w hadmw with ⟨h, -⟩ | ⟨-, -, -, -, h⟩ | ⟨-, h, -⟩
      · exfalso
        have : P.b * w < P.b * W := mul_lt_mul_of_pos_left hwW hb
        linarith
      · rw [h] at h1; linarith
      · linarith
    rcases hV σ.w hwσ with ⟨-, h⟩ | ⟨hwa, hwle, hq, hp, h⟩ | ⟨-, -, -, -, h⟩
    · linarith
    · have hws : σ.w = W := by
        by_contra hne
        have := (hmono hc1.le σ.w hwle).2 (lt_of_le_of_ne hwle hne)
        rw [h] at hVge; linarith
      have hpos : 0 < P.a - P.b * (σ.w / P.α) := by
        rw [hws, mul_div_assoc', sub_pos, div_lt_iff₀ hα0]; linarith
      obtain ⟨e1, e3⟩ := out_cand2 P hP c σ hQ hq hp hpos
      have e2 : piS P c .OA σ = (σ.w - c) * ((P.a - P.b * (σ.w / P.α)) / (2 * P.α)) := by
        rw [hpiS, h]
      unfold outcome
      rw [e1, e2, e3, hws]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> field_simp <;> ring
    · rw [h] at hVge; linarith [hG2le σ.w]
  · -- high cost: the non-inflated optimum `w₂`
    have hC' : cOA2 P < c := lt_of_le_of_lt (le_max_right _ _) hC
    have hc1 : cOA1 P ≤ c := by linarith
    have hW2' := hW2 hc1
    have hadm : wAdm P c .OA w2 := hwAdm w2 (by
        have : P.b * c < P.b * w2 := by rw [hbw2]; linarith
        exact lt_of_mul_lt_mul_left this hb.le) (by rw [hbw2]; nlinarith)
    have hVw2 : supplierValue P c .OA σ w2 = (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * P.μ) := by
      rcases hV w2 hadm with ⟨h, -⟩ | ⟨-, h, -, -, -⟩ | ⟨-, -, -, -, h⟩
      · exfalso; rw [hbw2] at h; linarith
      · exfalso; linarith
      · rw [h, hG2g, hw2]; ring
    have hge := hopt w2 hadm
    rw [hVw2] at hge
    have hgap : (W - c) * ((P.a - P.b * (W / P.α)) / (2 * P.α)) <
        (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * P.μ) := by
      have h3 := hpos c hC'
      have : 0 < (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * P.μ) -
          (W - c) * ((P.a - P.b * (W / P.α)) / (2 * P.α)) := by
        rw [hPrel]; exact div_pos h3 hden
      linarith
    rcases hV σ.w hwσ with ⟨-, h⟩ | ⟨-, hwle, -, -, h⟩ | ⟨hwa, -, hq, hp, h⟩
    · linarith
    · rw [h] at hge; linarith [(hmono hc1 σ.w hwle).1]
    · rw [h, hG2g] at hge
      have hsq : (σ.w - (P.a * P.μ + P.b * c) / (2 * P.b)) ^ 2 = 0 := by
        have : 0 ≤ P.b / (2 * P.μ) * (σ.w - (P.a * P.μ + P.b * c) / (2 * P.b)) ^ 2 := by
          positivity
        have h0 : P.b / (2 * P.μ) * (σ.w - (P.a * P.μ + P.b * c) / (2 * P.b)) ^ 2 = 0 := by
          linarith
        rcases mul_eq_zero.mp h0 with h' | h'
        · exfalso; have : 0 < P.b / (2 * P.μ) := by positivity
          linarith
        · exact h'
      have hws : σ.w = w2 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
        rw [hw2]; linarith
      have hpos2 : 0 < P.a - P.b * (σ.w / P.μ) := by
        rw [hws, mul_div_assoc', sub_pos, div_lt_iff₀ hμ0, hbw2]; linarith
      obtain ⟨e1, e3⟩ := out_cand1 P hP c σ hQ hq hp hpos2
      have e2 : piS P c .OA σ = (σ.w - c) * ((P.a - P.b * (σ.w / P.μ)) / 2) := by
        rw [hpiS, h]
      unfold outcome OA3
      rw [e1, e2, e3, hws, hw2]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> field_simp <;> ring

