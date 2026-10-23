-- Prove2me | solution 1 for YieldPostpone.Payment.lemma_1
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-23T04:16:37.672448+00:00
-- url     : https://prove2.me/submissions/dbfad60d-b093-46d4-934f-9e559138c5f9

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

theorem solution : ¬ (∀ (P : Params) (hP : P.Valid),
    cOA1 P < cOA2 P ∧ cOA2 P < P.a * P.μ / P.b ∧
    ∀ c, costAdm P c →
      (∃ σ : Profile, IsSPE P c .OA σ) ∧
      (∀ σ : Profile, IsSPE P c .OA σ →
        (c < max 0 (cOA1 P) → outcome P c .OA σ = OA1 P c) ∧
        (max 0 (cOA1 P) < c ∧ c < max 0 (cOA2 P) →
          outcome P c .OA σ = OA2 P c) ∧
        (max 0 (cOA2 P) < c → outcome P c .OA σ = OA3 P c))) := by
  intro H
  set P : Params := ⟨1, 1, 3 / 10, 3 / 35⟩ with hPdef
  have hP : P.Valid := by
    simp only [Params.Valid, hPdef]; norm_num
  have hμ : P.μ = 9 / 25 := by simp only [Params.μ, hPdef]; norm_num
  have hs : Real.sqrt P.μ = 3 / 5 := by
    rw [hμ, show (9 / 25 : ℝ) = (3 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hwhat : what P = 6 / 25 := by
    unfold what; rw [hs, hμ]; simp only [hPdef]; norm_num
  have hc1 : cOA1 P = 9 / 50 := by
    unfold cOA1; rw [hs, hμ]; simp only [hPdef]; norm_num
  have hc2 : cOA2 P = (-(27 / 1250) + Real.sqrt (1458 / 390625)) / (9 / 50) := by
    unfold cOA2; rw [hwhat, hμ]; simp only [hPdef]; norm_num
  have hsq : (279 / 5000 : ℝ) < Real.sqrt (1458 / 390625) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  set c : ℝ := 19 / 100 with hcdef
  have hc : costAdm P c := by
    refine ⟨by norm_num, ?_⟩
    rw [hμ]; simp only [hPdef]; norm_num
  obtain ⟨-, -, H3⟩ := H P hP
  obtain ⟨⟨σ, hσ⟩, hU⟩ := H3 c hc
  have hmid : max 0 (cOA1 P) < c ∧ c < max 0 (cOA2 P) := by
    refine ⟨?_, lt_of_lt_of_le ?_ (le_max_right _ _)⟩
    · rw [hc1]; norm_num
    · rw [hc2, lt_div_iff₀ (by norm_num)]; linarith
  have hout := (hU σ hσ).2.1 hmid
  have hR : piR P c .OA σ = 1 / 100 := by
    have := congrArg Prod.fst hout
    simp only [outcome, OA2] at this
    rw [this, hwhat]; simp only [hPdef]; norm_num
  have hCS : CS P c .OA σ = 1 / 60 := by
    have := congrArg (fun x => x.2.2) hout
    simp only [outcome, OA2] at this
    rw [this, hwhat]; simp only [hPdef]; norm_num
  have hrel := PPL1.oa_rel P hP c (by norm_num) σ hσ
  rw [hR, hCS, hμ] at hrel
  simp only [hPdef] at hrel
  norm_num at hrel

