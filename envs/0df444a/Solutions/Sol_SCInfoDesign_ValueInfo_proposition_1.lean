-- Prove2me | solution 1 for SCInfoDesign.ValueInfo.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T18:34:47.137521+00:00
-- url     : https://prove2.me/submissions/0efaed8a-6772-4e64-92e2-b248bb7bc013

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_ValueInfo_Setting

open SCInfoDesign.ValueInfo

noncomputable def vi2_gc (a b Q : ℝ) : ℝ :=
  if Q ≤ a then (a + b) / 2 - Q else if Q ≤ b then (b - Q) ^ 2 / (2 * (b - a)) else 0

noncomputable def vi2_Fc (a b q : ℝ) : ℝ :=
  if q ≤ a then 0 else if q ≤ b then (q - a) / (b - a) else 1

lemma vi2_int_pos (a b Q : ℝ) (hab : a < b) :
    ∫ x in a..b, max (x - Q) 0 = (b - a) * vi2_gc a b Q := by
  have hba : (b - a) ≠ 0 := by linarith
  unfold vi2_gc
  split_ifs with h1 h2
  · have : ∫ x in a..b, max (x - Q) 0 = ∫ x in a..b, (x - Q) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hab.le] at hx
      simp only
      rw [max_eq_left (by linarith [hx.1])]
    rw [this, intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
      intervalIntegrable_const]
    simp [integral_id]
    ring
  · have hc : Continuous fun x : ℝ => max (x - Q) 0 := by fun_prop
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := Q)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    have e1 : ∫ x in a..Q, max (x - Q) 0 = ∫ x in a..Q, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by linarith)] at hx
      simp only
      rw [max_eq_right (by linarith [hx.2])]
    have e2 : ∫ x in Q..b, max (x - Q) 0 = ∫ x in Q..b, (x - Q) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le h2] at hx
      simp only
      rw [max_eq_left (by linarith [hx.1])]
    rw [e1, e2, intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
      intervalIntegrable_const]
    simp [integral_id]
    field_simp
    ring
  · have : ∫ x in a..b, max (x - Q) 0 = ∫ x in a..b, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hab.le] at hx
      simp only
      rw [max_eq_right (by linarith [hx.2])]
    rw [this]; simp

lemma vi2_mean_pos (a b Q : ℝ) (hab : a < b) :
    uniformMean a b (fun d => max (d - Q) 0) = vi2_gc a b Q := by
  unfold uniformMean
  rw [vi2_int_pos a b Q hab]
  field_simp [show b - a ≠ 0 by linarith]

lemma vi2_mean_supp (a b Q ξ : ℝ) (hab : a < b) :
    uniformMean a b
      (fun d => ξ * max (d - Q) 0 + (1 - ξ) * max (Q - d) 0) =
      vi2_gc a b Q - (1 - ξ) * ((a + b) / 2 - Q) := by
  have hpt : (fun d => ξ * max (d - Q) 0 + (1 - ξ) * max (Q - d) 0) =
      fun d => max (d - Q) 0 - (1 - ξ) * (d - Q) := by
    funext d
    rcases le_total d Q with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have hc : Continuous fun x : ℝ => max (x - Q) 0 := by fun_prop
  unfold uniformMean
  rw [hpt, intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
    (by apply Continuous.intervalIntegrable; fun_prop), vi2_int_pos a b Q hab,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    intervalIntegral.intervalIntegrable_id intervalIntegrable_const]
  simp [integral_id]
  field_simp [show b - a ≠ 0 by linarith]
  ring

lemma vi2_U (a b q Q : ℝ) (hab : a < b) :
    vi2_gc a b q - (1 - vi2_Fc a b q) * (Q - q) ≤ vi2_gc a b Q ∧
    (a < q → q < b → Q ≠ q →
      vi2_gc a b q - (1 - vi2_Fc a b q) * (Q - q) < vi2_gc a b Q) := by
  have hL : 0 < b - a := by linarith
  have hL' : b - a ≠ 0 := hL.ne'
  -- value of gc at Q
  have gQ : (Q ≤ a ∧ vi2_gc a b Q = (a + b) / 2 - Q) ∨
      (a < Q ∧ Q ≤ b ∧ vi2_gc a b Q = (b - Q) ^ 2 / (2 * (b - a))) ∨
      (b < Q ∧ vi2_gc a b Q = 0) := by
    unfold vi2_gc
    by_cases h1 : Q ≤ a
    · left; exact ⟨h1, by rw [if_pos h1]⟩
    · by_cases h2 : Q ≤ b
      · right; left; exact ⟨not_le.mp h1, h2, by rw [if_neg h1, if_pos h2]⟩
      · right; right; exact ⟨not_le.mp h2, by rw [if_neg h1, if_neg h2]⟩
  have gnn : 0 ≤ vi2_gc a b Q := by
    rcases gQ with ⟨h, e⟩ | ⟨h, h', e⟩ | ⟨h, e⟩ <;> rw [e]
    · linarith
    · positivity
  by_cases hq1 : q ≤ a
  · have e1 : vi2_gc a b q - (1 - vi2_Fc a b q) * (Q - q) = (a + b) / 2 - Q := by
      unfold vi2_gc vi2_Fc; rw [if_pos hq1, if_pos hq1]; ring
    rw [e1]
    refine ⟨?_, fun h => absurd h (not_lt.mpr hq1)⟩
    rcases gQ with ⟨h, e⟩ | ⟨h, h', e⟩ | ⟨h, e⟩ <;> rw [e]
    · have k : (b - Q) ^ 2 / (2 * (b - a)) - ((a + b) / 2 - Q) =
          (b - a - (b - Q)) ^ 2 / (2 * (b - a)) := by field_simp; ring
      have : 0 ≤ (b - a - (b - Q)) ^ 2 / (2 * (b - a)) := by positivity
      linarith
    · linarith
  by_cases hq2 : q ≤ b
  · have hq1' : a < q := not_le.mp hq1
    have e1 : vi2_gc a b q - (1 - vi2_Fc a b q) * (Q - q) =
        (b - q) ^ 2 / (2 * (b - a)) - (b - q) / (b - a) * (Q - q) := by
      unfold vi2_gc vi2_Fc; rw [if_neg hq1, if_pos hq2, if_neg hq1, if_pos hq2]
      congr 2; field_simp; ring
    rw [e1]
    rcases gQ with ⟨h, e⟩ | ⟨h, h', e⟩ | ⟨h, e⟩ <;> rw [e]
    · have k : (a + b) / 2 - Q - ((b - q) ^ 2 / (2 * (b - a)) - (b - q) / (b - a) * (Q - q)) =
          ((q - a) * ((b - Q) * 2 - (b - a) - (b - q))) / (2 * (b - a)) := by
        field_simp; ring
      have hn : 0 ≤ (q - a) * ((b - Q) * 2 - (b - a) - (b - q)) := by
        apply mul_nonneg <;> linarith
      have : 0 ≤ ((q - a) * ((b - Q) * 2 - (b - a) - (b - q))) / (2 * (b - a)) := by
        positivity
      refine ⟨by linarith, fun _ _ _ => ?_⟩
      have hp : 0 < (q - a) * ((b - Q) * 2 - (b - a) - (b - q)) := by
        apply mul_pos <;> linarith
      have : 0 < ((q - a) * ((b - Q) * 2 - (b - a) - (b - q))) / (2 * (b - a)) := by
        positivity
      linarith
    · have k : (b - Q) ^ 2 / (2 * (b - a)) -
          ((b - q) ^ 2 / (2 * (b - a)) - (b - q) / (b - a) * (Q - q)) =
          (Q - q) ^ 2 / (2 * (b - a)) := by
        field_simp; ring
      have : 0 ≤ (Q - q) ^ 2 / (2 * (b - a)) := by positivity
      refine ⟨by linarith, fun _ _ hne => ?_⟩
      have : 0 < (Q - q) ^ 2 / (2 * (b - a)) := by
        have : Q - q ≠ 0 := sub_ne_zero.mpr hne
        positivity
      linarith
    · have k : (0:ℝ) - ((b - q) ^ 2 / (2 * (b - a)) - (b - q) / (b - a) * (Q - q)) =
          (b - q) * (2 * (Q - q) - (b - q)) / (2 * (b - a)) := by
        field_simp; ring
      have : 0 ≤ (b - q) * (2 * (Q - q) - (b - q)) / (2 * (b - a)) := by
        apply div_nonneg _ (by positivity)
        apply mul_nonneg <;> linarith
      refine ⟨by linarith, fun _ hqb _ => ?_⟩
      have : 0 < (b - q) * (2 * (Q - q) - (b - q)) / (2 * (b - a)) := by
        apply div_pos _ (by positivity)
        apply mul_pos <;> linarith
      linarith
  · have e1 : vi2_gc a b q - (1 - vi2_Fc a b q) * (Q - q) = 0 := by
      unfold vi2_gc vi2_Fc; rw [if_neg hq1, if_neg hq2, if_neg hq1, if_neg hq2]; ring
    rw [e1]
    exact ⟨gnn, fun _ h => absurd h (by linarith [not_le.mp hq2])⟩

lemma vi2_Fc_lo (a b q : ℝ) (h : q ≤ a) : vi2_Fc a b q = 0 := by
  unfold vi2_Fc; rw [if_pos h]

lemma vi2_Fc_mid (a b q : ℝ) (hab : a < b) (h1 : a ≤ q) (h2 : q ≤ b) :
    vi2_Fc a b q = (q - a) / (b - a) := by
  unfold vi2_Fc
  by_cases h : q ≤ a
  · rw [if_pos h, show q = a by linarith]; simp
  · rw [if_neg h, if_pos h2]

lemma vi2_Fc_hi (a b q : ℝ) (hab : a < b) (h : b ≤ q) : vi2_Fc a b q = 1 := by
  unfold vi2_Fc
  rw [if_neg (by linarith)]
  by_cases h2 : q ≤ b
  · rw [if_pos h2, show q = b by linarith, div_self (by linarith)]
  · rw [if_neg h2]


lemma vi2_opt_iff (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (q : ℝ)
    (hF : p * vi2_Fc P.a₀ P.b₀ q + (1 - p) * vi2_Fc P.a₁ P.b₁ q = ξ) :
    ∀ Q, IsOptimalQuantity P ξ p Q ↔ Q = q := by
  obtain ⟨hp0, hp1⟩ := hp
  have h0 := hab₀
  have h1 := hab₁
  have hstrict : (0 < 1 - p ∧ P.a₁ < q ∧ q < P.b₁) ∨ (0 < p ∧ P.a₀ < q ∧ q < P.b₀) := by
    by_cases hpe : p = 1
    · right
      subst hpe
      simp only [one_mul, sub_self, zero_mul, add_zero] at hF
      refine ⟨one_pos, ?_, ?_⟩
      · by_contra hc
        rw [vi2_Fc_lo _ _ _ (not_lt.mp hc)] at hF; linarith
      · by_contra hc
        rw [vi2_Fc_hi _ _ _ h0 (not_lt.mp hc)] at hF; linarith
    have hp1' : p < 1 := lt_of_le_of_ne hp1 hpe
    by_cases hqa : q ≤ P.a₁
    · right
      rw [vi2_Fc_lo _ _ _ hqa] at hF
      simp only [mul_zero, add_zero] at hF
      have hpp : 0 < p := by
        rcases eq_or_lt_of_le hp0 with h | h
        · rw [← h] at hF; linarith
        · exact h
      refine ⟨hpp, ?_, by linarith⟩
      by_contra hc
      rw [vi2_Fc_lo _ _ _ (not_lt.mp hc)] at hF; linarith
    by_cases hqb : P.b₁ ≤ q
    · right
      rw [vi2_Fc_hi _ _ _ h1 hqb] at hF
      have hpp : 0 < p := by
        rcases eq_or_lt_of_le hp0 with h | h
        · rw [← h] at hF; linarith
        · exact h
      refine ⟨hpp, by linarith, ?_⟩
      by_contra hc
      rw [vi2_Fc_hi _ _ _ h0 (not_lt.mp hc)] at hF; linarith
    left
    exact ⟨by linarith, not_le.mp hqa, not_le.mp hqb⟩
  have hq0 : 0 ≤ q := by
    rcases hstrict with ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> linarith
  have hS : ∀ Q, supplierCost P ξ p Q =
      p * (vi2_gc P.a₀ P.b₀ Q - (1 - ξ) * ((P.a₀ + P.b₀) / 2 - Q)) +
      (1 - p) * (vi2_gc P.a₁ P.b₁ Q - (1 - ξ) * ((P.a₁ + P.b₁) / 2 - Q)) := by
    intro Q
    unfold supplierCost nvLoss
    rw [vi2_mean_supp _ _ _ _ h0, vi2_mean_supp _ _ _ _ h1]
  have hdiff : ∀ Q, supplierCost P ξ p Q - supplierCost P ξ p q =
      p * (vi2_gc P.a₀ P.b₀ Q - (vi2_gc P.a₀ P.b₀ q - (1 - vi2_Fc P.a₀ P.b₀ q) * (Q - q))) +
      (1 - p) * (vi2_gc P.a₁ P.b₁ Q -
        (vi2_gc P.a₁ P.b₁ q - (1 - vi2_Fc P.a₁ P.b₁ q) * (Q - q))) := by
    intro Q
    rw [hS, hS]
    linear_combination (Q - q) * hF
  have hge : ∀ Q, supplierCost P ξ p q ≤ supplierCost P ξ p Q := by
    intro Q
    have := hdiff Q
    have u0 := (vi2_U P.a₀ P.b₀ q Q h0).1
    have u1 := (vi2_U P.a₁ P.b₁ q Q h1).1
    have : 0 ≤ p * (vi2_gc P.a₀ P.b₀ Q -
        (vi2_gc P.a₀ P.b₀ q - (1 - vi2_Fc P.a₀ P.b₀ q) * (Q - q))) :=
      mul_nonneg hp0 (by linarith)
    have : 0 ≤ (1 - p) * (vi2_gc P.a₁ P.b₁ Q -
        (vi2_gc P.a₁ P.b₁ q - (1 - vi2_Fc P.a₁ P.b₁ q) * (Q - q))) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hgt : ∀ Q, Q ≠ q → supplierCost P ξ p q < supplierCost P ξ p Q := by
    intro Q hne
    have := hdiff Q
    have u0 := vi2_U P.a₀ P.b₀ q Q h0
    have u1 := vi2_U P.a₁ P.b₁ q Q h1
    have n0 : 0 ≤ p * (vi2_gc P.a₀ P.b₀ Q -
        (vi2_gc P.a₀ P.b₀ q - (1 - vi2_Fc P.a₀ P.b₀ q) * (Q - q))) :=
      mul_nonneg hp0 (by linarith [u0.1])
    have n1 : 0 ≤ (1 - p) * (vi2_gc P.a₁ P.b₁ Q -
        (vi2_gc P.a₁ P.b₁ q - (1 - vi2_Fc P.a₁ P.b₁ q) * (Q - q))) :=
      mul_nonneg (by linarith) (by linarith [u1.1])
    rcases hstrict with ⟨hpp, hlo, hhi⟩ | ⟨hpp, hlo, hhi⟩
    · have := mul_pos hpp (sub_pos.mpr (u1.2 hlo hhi hne))
      linarith
    · have := mul_pos hpp (sub_pos.mpr (u0.2 hlo hhi hne))
      linarith
  intro Q
  constructor
  · rintro ⟨_, hQ⟩
    by_contra hne
    have := hQ q hq0
    have := hgt Q hne
    linarith
  · rintro rfl
    exact ⟨hq0, fun Q' _ => hge Q'⟩

theorem vi2_prop1
    (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (τup P p ≤ ξ → ∀ Q : ℝ,
        IsOptimalQuantity P ξ p Q ↔ Q = P.b₀ - (P.b₀ - P.a₀) * (1 - ξ) / p) ∧
    (τlow P p ≤ ξ → ξ ≤ τup P p → ∀ Q : ℝ,
        IsOptimalQuantity P ξ p Q ↔
          Q = (P.b₁ * (ξ - τlow P p) + P.a₁ * (τup P p - ξ)) / (τup P p - τlow P p)) ∧
    (ξ ≤ τlow P p → ∀ Q : ℝ,
        IsOptimalQuantity P ξ p Q ↔ Q = ξ * (P.b₀ - P.a₀) / p + P.a₀) := by
  obtain ⟨hp0, hp1⟩ := hp
  have hB : 0 < P.b₀ - P.a₀ := by linarith
  have hL1 : 0 < P.b₁ - P.a₁ := by linarith
  have opt := vi2_opt_iff P hab₀ hab₁ ha₀ hnest_a hnest_b ξ hξ0 hξ1 p ⟨hp0, hp1⟩
  refine ⟨fun hτ => ?_, fun hτl hτu => ?_, fun hτ => ?_⟩
  · -- high regime
    unfold τup at hτ
    have hτ' : (1 - ξ) * (P.b₀ - P.a₀) ≤ p * (P.b₀ - P.b₁) := by
      have : 1 - ξ ≤ p * (P.b₀ - P.b₁) / (P.b₀ - P.a₀) := by linarith
      rwa [le_div_iff₀ hB] at this
    have hpp : 0 < p := by
      rcases eq_or_lt_of_le hp0 with h | h
      · rw [← h] at hτ'; nlinarith
      · exact h
    set t := (P.b₀ - P.a₀) * (1 - ξ) / p with ht_def
    have ht : t * p = (P.b₀ - P.a₀) * (1 - ξ) := div_mul_cancel₀ _ hpp.ne'
    have htpos : 0 < t := by positivity
    have hthi : t ≤ P.b₀ - P.b₁ := by nlinarith
    apply opt
    rw [vi2_Fc_mid _ _ _ hab₀ (by nlinarith) (by linarith),
      vi2_Fc_hi _ _ _ hab₁ (by linarith)]
    field_simp
    linear_combination -ht
  · -- middle regime
    unfold τup at hτu ⊢
    unfold τlow at hτl ⊢
    have hl : p * (P.a₁ - P.a₀) ≤ ξ * (P.b₀ - P.a₀) := by
      rwa [div_le_iff₀ hB] at hτl
    have hu : ξ * (P.b₀ - P.a₀) ≤ (P.b₀ - P.a₀) - p * (P.b₀ - P.b₁) := by
      have : p * (P.b₀ - P.b₁) / (P.b₀ - P.a₀) ≤ 1 - ξ := by linarith
      rw [div_le_iff₀ hB] at this; linarith
    set N := (1 - p) * (P.b₀ - P.a₀) + p * (P.b₁ - P.a₁) with hN
    have hNp : 0 < N := by
      rcases eq_or_lt_of_le hp0 with h | h
      · rw [hN, ← h]; linarith
      · have : 0 ≤ (1 - p) * (P.b₀ - P.a₀) := mul_nonneg (by linarith) hB.le
        have : 0 < p * (P.b₁ - P.a₁) := mul_pos h hL1
        linarith
    have hden : (1 - p * (P.b₀ - P.b₁) / (P.b₀ - P.a₀)) - p * (P.a₁ - P.a₀) / (P.b₀ - P.a₀)
        = N / (P.b₀ - P.a₀) := by
      rw [hN]; field_simp; ring
    set q := (P.b₁ * (ξ - p * (P.a₁ - P.a₀) / (P.b₀ - P.a₀)) +
      P.a₁ * ((1 - p * (P.b₀ - P.b₁) / (P.b₀ - P.a₀)) - ξ)) /
      ((1 - p * (P.b₀ - P.b₁) / (P.b₀ - P.a₀)) - p * (P.a₁ - P.a₀) / (P.b₀ - P.a₀)) with hq
    have hq' : q * N = P.b₁ * (ξ * (P.b₀ - P.a₀) - p * (P.a₁ - P.a₀)) +
        P.a₁ * ((P.b₀ - P.a₀) - p * (P.b₀ - P.b₁) - ξ * (P.b₀ - P.a₀)) := by
      rw [hq, hden]; field_simp
    have hqlo : P.a₁ ≤ q := by
      have : P.a₁ * N ≤ q * N := by rw [hq', hN]; nlinarith
      exact le_of_mul_le_mul_right this hNp
    have hqhi : q ≤ P.b₁ := by
      have : q * N ≤ P.b₁ * N := by rw [hq', hN]; nlinarith
      exact le_of_mul_le_mul_right this hNp
    apply opt
    rw [vi2_Fc_mid _ _ _ hab₀ (by linarith) (by linarith),
      vi2_Fc_mid _ _ _ hab₁ hqlo hqhi]
    have hB' := hB.ne'
    have hL1' := hL1.ne'
    field_simp
    rw [hN] at hq'
    linear_combination hq'
  · -- low regime
    unfold τlow at hτ
    have hl : ξ * (P.b₀ - P.a₀) ≤ p * (P.a₁ - P.a₀) := by
      rwa [le_div_iff₀ hB] at hτ
    have hpp : 0 < p := by
      rcases eq_or_lt_of_le hp0 with h | h
      · rw [← h] at hl; nlinarith [mul_pos hξ0 hB]
      · exact h
    set t := ξ * (P.b₀ - P.a₀) / p with ht_def
    have ht : t * p = ξ * (P.b₀ - P.a₀) := div_mul_cancel₀ _ hpp.ne'
    have htpos : 0 < t := by positivity
    have hthi : t ≤ P.a₁ - P.a₀ := by
      have : t * p ≤ (P.a₁ - P.a₀) * p := by rw [ht]; linarith
      exact le_of_mul_le_mul_right this hpp
    apply opt
    rw [vi2_Fc_lo _ _ _ (by linarith : t + P.a₀ ≤ P.a₁),
      vi2_Fc_mid _ _ _ hab₀ (by linarith) (by linarith)]
    field_simp
    linear_combination ht

theorem solution
    (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (τup P p ≤ ξ → ∀ Q : ℝ,
        IsOptimalQuantity P ξ p Q ↔ Q = P.b₀ - (P.b₀ - P.a₀) * (1 - ξ) / p) ∧
    (τlow P p ≤ ξ → ξ ≤ τup P p → ∀ Q : ℝ,
        IsOptimalQuantity P ξ p Q ↔
          Q = (P.b₁ * (ξ - τlow P p) + P.a₁ * (τup P p - ξ)) / (τup P p - τlow P p)) ∧
    (ξ ≤ τlow P p → ∀ Q : ℝ,
        IsOptimalQuantity P ξ p Q ↔ Q = ξ * (P.b₀ - P.a₀) / p + P.a₀) :=
  vi2_prop1 P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1 p hp
