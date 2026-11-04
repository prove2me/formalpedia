-- Prove2me | solution 1 for SCInfoDesign.ValueInfo.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T18:41:20.793245+00:00
-- url     : https://prove2.me/submissions/4ce6bba4-0f81-4327-96fd-312904914b29

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

lemma vi2_gc_lo (a b Q : ℝ) (h : Q ≤ a) : vi2_gc a b Q = (a + b) / 2 - Q := by
  unfold vi2_gc; rw [if_pos h]

lemma vi2_gc_mid (a b Q : ℝ) (hab : a < b) (h1 : a ≤ Q) (h2 : Q ≤ b) :
    vi2_gc a b Q = (b - Q) ^ 2 / (2 * (b - a)) := by
  unfold vi2_gc
  by_cases h : Q ≤ a
  · rw [if_pos h, show Q = a by linarith]
    have : b - a ≠ 0 := by linarith
    field_simp; ring
  · rw [if_neg h, if_pos h2]

/-- the supporting line of `K` (the extended chord from `p̂` to `1`) -/
noncomputable def vi2_L (P : Params) (ξ p : ℝ) : ℝ :=
  (-(P.a₀ * ξ ^ 2 - P.a₀ * ξ - P.a₁ * ξ + P.a₁ - P.b₀ * ξ ^ 2 + 2 * P.b₀ * ξ - P.b₁)) / 2 +
    p * ((P.a₁ - P.a₀) * (1 - ξ) + (P.b₀ - P.b₁)) / 2

lemma vi2_low (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1)
    (hl : ξ * (P.b₀ - P.a₀) ≤ p * (P.a₁ - P.a₀)) :
    (∀ Q, IsOptimalQuantity P ξ p Q ↔ Q = ξ * (P.b₀ - P.a₀) / p + P.a₀) ∧
    retailerCost P p (ξ * (P.b₀ - P.a₀) / p + P.a₀) =
      vi2_L P ξ p + (1 - p) * (2 - ξ) * (p * (P.a₁ - P.a₀) - ξ * (P.b₀ - P.a₀)) / (2 * p) := by
  obtain ⟨hp0, hp1⟩ := hp
  have hB : 0 < P.b₀ - P.a₀ := by linarith
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
  refine ⟨?_, ?_⟩
  · apply vi2_opt_iff P hab₀ hab₁ ha₀ hnest_a hnest_b ξ hξ0 hξ1 p ⟨hp0, hp1⟩
    rw [vi2_Fc_lo _ _ _ (by linarith : t + P.a₀ ≤ P.a₁),
      vi2_Fc_mid _ _ _ hab₀ (by linarith) (by linarith)]
    field_simp
    linear_combination ht
  · unfold retailerCost
    rw [vi2_mean_pos _ _ _ hab₀, vi2_mean_pos _ _ _ hab₁,
      vi2_gc_mid _ _ _ hab₀ (by linarith) (by linarith), vi2_gc_lo _ _ _ (by linarith)]
    rw [ht_def]
    unfold vi2_L
    field_simp
    ring

lemma vi2_mid (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1)
    (hl : p * (P.a₁ - P.a₀) ≤ ξ * (P.b₀ - P.a₀))
    (hu : ξ * (P.b₀ - P.a₀) ≤ (P.b₀ - P.a₀) - p * (P.b₀ - P.b₁)) :
    let N := (1 - p) * (P.b₀ - P.a₀) + p * (P.b₁ - P.a₁)
    let q := (P.b₁ * (ξ * (P.b₀ - P.a₀) - p * (P.a₁ - P.a₀)) +
        P.a₁ * ((P.b₀ - P.a₀) - p * (P.b₀ - P.b₁) - ξ * (P.b₀ - P.a₀))) / N
    0 < N ∧ (∀ Q, IsOptimalQuantity P ξ p Q ↔ Q = q) ∧
    retailerCost P p q = vi2_L P ξ p + (1 - p) * (ξ * (P.b₀ - P.a₀) - p * (P.a₁ - P.a₀)) *
      ((P.a₁ - P.a₀) * (1 - ξ) + (P.b₀ - P.b₁) * (2 - ξ)) / (2 * N) := by
  intro N q
  obtain ⟨hp0, hp1⟩ := hp
  have hB : 0 < P.b₀ - P.a₀ := by linarith
  have hL1 : 0 < P.b₁ - P.a₁ := by linarith
  have hNp : 0 < N := by
    rcases eq_or_lt_of_le hp0 with h | h
    · show 0 < (1 - p) * (P.b₀ - P.a₀) + p * (P.b₁ - P.a₁)
      rw [← h]; linarith
    · have : 0 ≤ (1 - p) * (P.b₀ - P.a₀) := mul_nonneg (by linarith) hB.le
      have : 0 < p * (P.b₁ - P.a₁) := mul_pos h hL1
      show 0 < (1 - p) * (P.b₀ - P.a₀) + p * (P.b₁ - P.a₁)
      linarith
  have hq' : q * N = P.b₁ * (ξ * (P.b₀ - P.a₀) - p * (P.a₁ - P.a₀)) +
      P.a₁ * ((P.b₀ - P.a₀) - p * (P.b₀ - P.b₁) - ξ * (P.b₀ - P.a₀)) :=
    div_mul_cancel₀ _ hNp.ne'
  have hN : N = (1 - p) * (P.b₀ - P.a₀) + p * (P.b₁ - P.a₁) := rfl
  have hqlo : P.a₁ ≤ q := by
    have : P.a₁ * N ≤ q * N := by rw [hq', hN]; nlinarith
    exact le_of_mul_le_mul_right this hNp
  have hqhi : q ≤ P.b₁ := by
    have : q * N ≤ P.b₁ * N := by rw [hq', hN]; nlinarith
    exact le_of_mul_le_mul_right this hNp
  refine ⟨hNp, ?_, ?_⟩
  · apply vi2_opt_iff P hab₀ hab₁ ha₀ hnest_a hnest_b ξ hξ0 hξ1 p ⟨hp0, hp1⟩
    rw [vi2_Fc_mid _ _ _ hab₀ (by linarith) (by linarith),
      vi2_Fc_mid _ _ _ hab₁ hqlo hqhi]
    have hB' := hB.ne'
    have hL1' := hL1.ne'
    field_simp
    rw [hN] at hq'
    linear_combination hq'
  · unfold retailerCost
    rw [vi2_mean_pos _ _ _ hab₀, vi2_mean_pos _ _ _ hab₁,
      vi2_gc_mid _ _ _ hab₀ (by linarith) (by linarith), vi2_gc_mid _ _ _ hab₁ hqlo hqhi]
    have hq : q = (P.b₁ * (ξ * (P.b₀ - P.a₀) - p * (P.a₁ - P.a₀)) +
        P.a₁ * ((P.b₀ - P.a₀) - p * (P.b₀ - P.b₁) - ξ * (P.b₀ - P.a₀))) / N := rfl
    rw [hq]
    unfold vi2_L
    have hB' := hB.ne'
    have hL1' := hL1.ne'
    have hN' := hNp.ne'
    field_simp
    rw [hN]
    ring

section vi2main
variable (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀) (hlt : P.a₀ < P.a₁)

include hab₀ hab₁ ha₀ hnest_a hnest_b hlt

lemma vi2_xi_lt_one (ξ : ℝ) (hξ : ξ * (P.b₀ - P.a₀) ≤ P.a₁ - P.a₀) : ξ < 1 := by
  by_contra h
  have : (P.b₀ - P.a₀) ≤ ξ * (P.b₀ - P.a₀) := by nlinarith
  linarith

/-- In the regime `ξ ≤ (a₁-a₀)/(b₀-a₀)`: unique optimum for every belief, and its retailer cost
dominates the line `L`. -/
lemma vi2_uniq (ξ : ℝ) (hξ0 : 0 < ξ) (hξ : ξ * (P.b₀ - P.a₀) ≤ P.a₁ - P.a₀)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    ∃ q, (∀ Q, IsOptimalQuantity P ξ p Q ↔ Q = q) ∧ vi2_L P ξ p ≤ retailerCost P p q := by
  have hξ1 := vi2_xi_lt_one P hab₀ hab₁ ha₀ hnest_a hnest_b hlt ξ hξ
  obtain ⟨hp0, hp1⟩ := hp
  rcases le_total (ξ * (P.b₀ - P.a₀)) (p * (P.a₁ - P.a₀)) with hl | hl
  · obtain ⟨h1, h2⟩ := vi2_low P hab₀ hab₁ ha₀ hnest_a hnest_b ξ hξ0 hξ1 p ⟨hp0, hp1⟩ hl
    refine ⟨_, h1, ?_⟩
    rw [h2]
    have hpp : 0 < p := by
      rcases eq_or_lt_of_le hp0 with h | h
      · rw [← h] at hl; nlinarith [mul_pos hξ0 (show 0 < P.b₀ - P.a₀ by linarith)]
      · exact h
    have : 0 ≤ (1 - p) * (2 - ξ) * (p * (P.a₁ - P.a₀) - ξ * (P.b₀ - P.a₀)) / (2 * p) := by
      apply div_nonneg _ (by positivity)
      apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    linarith
  · have hu : ξ * (P.b₀ - P.a₀) ≤ (P.b₀ - P.a₀) - p * (P.b₀ - P.b₁) := by nlinarith
    obtain ⟨hN, h1, h2⟩ := vi2_mid P hab₀ hab₁ ha₀ hnest_a hnest_b ξ hξ0 hξ1 p ⟨hp0, hp1⟩ hl hu
    refine ⟨_, h1, ?_⟩
    rw [h2]
    have hC : 0 < (P.a₁ - P.a₀) * (1 - ξ) + (P.b₀ - P.b₁) * (2 - ξ) := by
      have := mul_pos (show 0 < P.a₁ - P.a₀ by linarith) (show 0 < 1 - ξ by linarith)
      have := mul_nonneg (show 0 ≤ P.b₀ - P.b₁ by linarith) (show 0 ≤ 2 - ξ by linarith)
      linarith
    have : 0 ≤ (1 - p) * (ξ * (P.b₀ - P.a₀) - p * (P.a₁ - P.a₀)) *
        ((P.a₁ - P.a₀) * (1 - ξ) + (P.b₀ - P.b₁) * (2 - ξ)) /
        (2 * ((1 - p) * (P.b₀ - P.a₀) + p * (P.b₁ - P.a₁))) := by
      apply div_nonneg _ (by positivity)
      apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) hC.le
    linarith

lemma vi2_prefQ (ξ p q : ℝ) (h : ∀ Q, IsOptimalQuantity P ξ p Q ↔ Q = q) :
    prefQ P ξ p = q := by
  have hset : {Q | IsOptimalQuantity P ξ p Q} = {q} := Set.ext fun Q => h Q
  show sSup {Q | IsOptimalQuantity P ξ p Q} = q
  rw [hset, csSup_singleton]

omit hab₀ hab₁ ha₀ hnest_a hnest_b hlt in
lemma vi2_realize (ξ : ℝ) (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0:ℝ) 1) (n : ℕ)
    (w q : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hq : ∀ i, q i ∈ Set.Icc (0:ℝ) 1) (hwq : ∑ i, w i * q i = p₀) :
    ∃ π : Fin 2 → Fin n → ℝ, IsPolicy π ∧
      expectedCost P p₀ π (prefQ P ξ) = ∑ i, w i * K P ξ (q i) := by
  obtain ⟨hp0, hp1⟩ := hp₀
  have hwq_nn : ∀ i, 0 ≤ w i * q i := fun i => mul_nonneg (hw i) (hq i).1
  have hw1q_nn : ∀ i, 0 ≤ w i * (1 - q i) := fun i => mul_nonneg (hw i) (by linarith [(hq i).2])
  have hsum1q : ∑ i, w i * (1 - q i) = 1 - p₀ := by
    simp_rw [mul_sub, mul_one]; rw [Finset.sum_sub_distrib, hw1, hwq]
  let π : Fin 2 → Fin n → ℝ := ![fun i => if p₀ = 0 then w i else w i * q i / p₀,
    fun i => if p₀ = 1 then w i else w i * (1 - q i) / (1 - p₀)]
  have hπ0 : ∀ i, π 0 i = if p₀ = 0 then w i else w i * q i / p₀ := fun i => rfl
  have hπ1 : ∀ i, π 1 i = if p₀ = 1 then w i else w i * (1 - q i) / (1 - p₀) := fun i => rfl
  have hmsg : ∀ i, msgProb p₀ π i = w i := by
    intro i
    unfold msgProb
    rw [hπ0, hπ1]
    by_cases h0 : p₀ = 0
    · have h1 : p₀ ≠ 1 := by rw [h0]; norm_num
      rw [if_pos h0, if_neg h1, h0]
      have : w i * q i = 0 := by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hwq_nn j)).mp (by rw [hwq, h0])
        exact this i (Finset.mem_univ i)
      simp; linear_combination -this
    · by_cases h1 : p₀ = 1
      · rw [if_neg h0, if_pos h1, h1]
        have : w i * (1 - q i) = 0 := by
          have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hw1q_nn j)).mp
            (by rw [hsum1q, h1]; ring)
          exact this i (Finset.mem_univ i)
        simp; linear_combination -this
      · rw [if_neg h0, if_neg h1]
        have : 1 - p₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
        field_simp
        ring
  refine ⟨π, ⟨?_, ?_⟩, ?_⟩
  · intro ω i
    fin_cases ω
    · show 0 ≤ π 0 i
      rw [hπ0]; split_ifs
      · exact hw i
      · exact div_nonneg (hwq_nn i) hp0
    · show 0 ≤ π 1 i
      rw [hπ1]; split_ifs
      · exact hw i
      · exact div_nonneg (hw1q_nn i) (by linarith)
  · intro ω
    fin_cases ω
    · show ∑ i, π 0 i = 1
      simp_rw [hπ0]
      by_cases h0 : p₀ = 0
      · simp only [if_pos h0]; exact hw1
      · simp only [if_neg h0]; rw [← Finset.sum_div, hwq, div_self h0]
    · show ∑ i, π 1 i = 1
      simp_rw [hπ1]
      by_cases h1 : p₀ = 1
      · simp only [if_pos h1]; exact hw1
      · simp only [if_neg h1]
        rw [← Finset.sum_div, hsum1q, div_self (sub_ne_zero.mpr (Ne.symm h1))]
  · unfold expectedCost
    apply Finset.sum_congr rfl
    intro i _
    rw [hmsg i]
    show w i * K P ξ (posterior p₀ π i) = w i * K P ξ (q i)
    by_cases hwi : w i = 0
    · rw [hwi]; ring
    congr 2
    unfold posterior
    rw [hmsg i, hπ0]
    by_cases h0 : p₀ = 0
    · rw [if_pos h0, h0]
      have : w i * q i = 0 := by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hwq_nn j)).mp (by rw [hwq, h0])
        exact this i (Finset.mem_univ i)
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hwi
      · rw [h]; simp
    · rw [if_neg h0]
      field_simp

/-- K on the low branch -/
lemma vi2_K_low (ξ : ℝ) (hξ0 : 0 < ξ) (hξ : ξ * (P.b₀ - P.a₀) ≤ P.a₁ - P.a₀)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (hl : ξ * (P.b₀ - P.a₀) ≤ p * (P.a₁ - P.a₀)) :
    K P ξ p =
      vi2_L P ξ p + (1 - p) * (2 - ξ) * (p * (P.a₁ - P.a₀) - ξ * (P.b₀ - P.a₀)) / (2 * p) := by
  have hξ1 := vi2_xi_lt_one P hab₀ hab₁ ha₀ hnest_a hnest_b hlt ξ hξ
  obtain ⟨h1, h2⟩ := vi2_low P hab₀ hab₁ ha₀ hnest_a hnest_b ξ hξ0 hξ1 p hp hl
  unfold K
  rw [vi2_prefQ P hab₀ hab₁ ha₀ hnest_a hnest_b hlt ξ p _ h1, h2]

lemma vi2_K_zero (ξ : ℝ) (hξ0 : 0 < ξ) (hξ : ξ * (P.b₀ - P.a₀) ≤ P.a₁ - P.a₀) :
    K P ξ 0 = vi2_L P ξ 0 + ξ * ((P.a₁ - P.a₀) * (1 - ξ) + (P.b₀ - P.b₁) * (2 - ξ)) / 2 := by
  have hξ1 := vi2_xi_lt_one P hab₀ hab₁ ha₀ hnest_a hnest_b hlt ξ hξ
  have hB : 0 < P.b₀ - P.a₀ := by linarith
  obtain ⟨hN, h1, h2⟩ := vi2_mid P hab₀ hab₁ ha₀ hnest_a hnest_b ξ hξ0 hξ1 0
    ⟨le_refl _, zero_le_one⟩ (by nlinarith) (by nlinarith)
  unfold K
  rw [vi2_prefQ P hab₀ hab₁ ha₀ hnest_a hnest_b hlt ξ 0 _ h1, h2]
  field_simp
  ring

/-- the value of the design problem in the partial-disclosure regime -/
lemma vi2_value (ξ : ℝ) (hξ0 : 0 < ξ) (hξ : ξ * (P.b₀ - P.a₀) ≤ P.a₁ - P.a₀)
    (p₀ : ℝ) (hp₁ : p₀ ≤ 1) (hl : ξ * (P.b₀ - P.a₀) ≤ p₀ * (P.a₁ - P.a₀)) :
    optimalCost P ξ p₀ = vi2_L P ξ p₀ := by
  have hB : 0 < P.b₀ - P.a₀ := by linarith
  have hA : 0 < P.a₁ - P.a₀ := by linarith
  have hp0 : 0 < p₀ := by
    by_contra h
    have : p₀ * (P.a₁ - P.a₀) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hA.le
    nlinarith [mul_pos hξ0 hB]
  set ph := ξ * (P.b₀ - P.a₀) / (P.a₁ - P.a₀) with hph
  have hph_eq : ph * (P.a₁ - P.a₀) = ξ * (P.b₀ - P.a₀) := div_mul_cancel₀ _ hA.ne'
  have hph0 : 0 < ph := by positivity
  have hphp : ph ≤ p₀ := by
    have : ph * (P.a₁ - P.a₀) ≤ p₀ * (P.a₁ - P.a₀) := by rw [hph_eq]; exact hl
    exact le_of_mul_le_mul_right this hA
  -- K = L at ph and at 1
  have hKph : K P ξ ph = vi2_L P ξ ph := by
    rw [vi2_K_low P hab₀ hab₁ ha₀ hnest_a hnest_b hlt ξ hξ0 hξ ph ⟨hph0.le, by linarith⟩
      (by rw [hph_eq])]
    rw [hph_eq]; simp
  have hK1 : K P ξ 1 = vi2_L P ξ 1 := by
    rw [vi2_K_low P hab₀ hab₁ ha₀ hnest_a hnest_b hlt ξ hξ0 hξ 1 ⟨zero_le_one, le_refl _⟩
      (by linarith)]
    simp
  have hBR : IsBestResponseProfile P ξ (prefQ P ξ) := by
    intro p hp
    obtain ⟨q, hq, -⟩ := vi2_uniq P hab₀ hab₁ ha₀ hnest_a hnest_b hlt ξ hξ0 hξ p hp
    rw [vi2_prefQ P hab₀ hab₁ ha₀ hnest_a hnest_b hlt ξ p q hq]
    exact (hq q).2 rfl
  -- lower bound
  have hlow : ∀ c ∈ {c : ℝ | ∃ (n : ℕ) (π : Fin 2 → Fin n → ℝ) (Qs : ℝ → ℝ),
      IsPolicy π ∧ IsBestResponseProfile P ξ Qs ∧ c = expectedCost P p₀ π Qs},
      vi2_L P ξ p₀ ≤ c := by
    rintro c ⟨n, π, Qs, hπ, hQs, rfl⟩
    set w : Fin n → ℝ := fun m => msgProb p₀ π m with hw_def
    set q : Fin n → ℝ := fun m => posterior p₀ π m with hq_def
    have hwnn : ∀ m, 0 ≤ w m := fun m => by
      simp only [hw_def, msgProb]
      have := hπ.1 0 m; have := hπ.1 1 m
      have : 0 ≤ 1 - p₀ := by linarith
      positivity
    have hw1 : ∑ m, w m = 1 := by
      simp only [hw_def, msgProb]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hπ.2 0, hπ.2 1]; ring
    have hwq : ∀ m, w m * q m = p₀ * π 0 m := by
      intro m
      simp only [hw_def, hq_def, posterior]
      by_cases h : msgProb p₀ π m = 0
      · rw [h]
        have a1 : 0 ≤ p₀ * π 0 m := mul_nonneg hp0.le (hπ.1 0 m)
        have a2 : 0 ≤ (1 - p₀) * π 1 m := mul_nonneg (by linarith) (hπ.1 1 m)
        unfold msgProb at h
        rw [zero_mul]; linarith
      · field_simp
    have hqI : ∀ m, q m ∈ Set.Icc (0:ℝ) 1 := by
      intro m
      simp only [hq_def, posterior, msgProb]
      have a1 : 0 ≤ p₀ * π 0 m := mul_nonneg hp0.le (hπ.1 0 m)
      have a2 : 0 ≤ (1 - p₀) * π 1 m := mul_nonneg (by linarith) (hπ.1 1 m)
      refine ⟨div_nonneg a1 (by linarith), ?_⟩
      rcases eq_or_lt_of_le (add_nonneg a1 a2) with h | h
      · rw [← h, div_zero]; norm_num
      · rw [div_le_one h]; linarith
    have hsum : ∑ m, w m * q m = p₀ := by
      simp_rw [hwq]; rw [← Finset.mul_sum, hπ.2 0, mul_one]
    have hLsum : ∑ m, w m * vi2_L P ξ (q m) = vi2_L P ξ p₀ := by
      have e : ∀ m, w m * vi2_L P ξ (q m) = w m * vi2_L P ξ 0 +
          (w m * q m) * (((P.a₁ - P.a₀) * (1 - ξ) + (P.b₀ - P.b₁)) / 2) := by
        intro m; unfold vi2_L; ring
      simp_rw [e]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hw1, hsum]
      unfold vi2_L; ring
    rw [← hLsum]
    unfold expectedCost
    apply Finset.sum_le_sum
    intro m _
    obtain ⟨qq, hqq, hLq⟩ := vi2_uniq P hab₀ hab₁ ha₀ hnest_a hnest_b hlt ξ hξ0 hξ (q m) (hqI m)
    have hQ : Qs (q m) = qq := (hqq _).1 (hQs (q m) (hqI m))
    show w m * vi2_L P ξ (q m) ≤ w m * retailerCost P (q m) (Qs (q m))
    rw [hQ]
    exact mul_le_mul_of_nonneg_left hLq (hwnn m)
  -- an attaining policy
  have hmem : vi2_L P ξ p₀ ∈ {c : ℝ | ∃ (n : ℕ) (π : Fin 2 → Fin n → ℝ) (Qs : ℝ → ℝ),
      IsPolicy π ∧ IsBestResponseProfile P ξ Qs ∧ c = expectedCost P p₀ π Qs} := by
    obtain ⟨t, ht0, ht1, htp⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (1 - t) * ph + t = p₀ := by
      rcases eq_or_lt_of_le hp₁ with h | h
      · exact ⟨1, zero_le_one, le_refl _, by rw [h]; ring⟩
      · have h1 : 0 < 1 - ph := by linarith
        refine ⟨(p₀ - ph) / (1 - ph), div_nonneg (by linarith) h1.le, ?_, ?_⟩
        · rw [div_le_one h1]; linarith
        · field_simp; ring
    obtain ⟨π, hπ, hcost⟩ := vi2_realize P ξ p₀ ⟨hp0.le, hp₁⟩ 2 ![1 - t, t] ![ph, 1]
      (fun i => by fin_cases i <;> simp <;> linarith)
      (by simp)
      (fun i => by fin_cases i <;> simp <;> constructor <;> linarith)
      (by simp; linarith)
    refine ⟨2, π, prefQ P ξ, hπ, hBR, ?_⟩
    rw [hcost]
    simp [hKph, hK1]
    rw [← htp]
    unfold vi2_L
    ring
  have hne : Set.Nonempty {c : ℝ | ∃ (n : ℕ) (π : Fin 2 → Fin n → ℝ) (Qs : ℝ → ℝ),
      IsPolicy π ∧ IsBestResponseProfile P ξ Qs ∧ c = expectedCost P p₀ π Qs} := ⟨_, hmem⟩
  unfold optimalCost
  exact le_antisymm (csInf_le ⟨_, hlow⟩ hmem) (le_csInf hne hlow)

end vi2main

section vi2final
variable (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀) (hlt : P.a₀ < P.a₁)

include hab₀ hab₁ ha₀ hnest_a hnest_b hlt

lemma vi2_VI_ND (ξ : ℝ) (hξ0 : 0 < ξ) (hξ : ξ * (P.b₀ - P.a₀) ≤ P.a₁ - P.a₀)
    (p₀ : ℝ) (hp₁ : p₀ ≤ 1) (hl : ξ * (P.b₀ - P.a₀) ≤ p₀ * (P.a₁ - P.a₀)) :
    VI_ND P ξ p₀ = (1 - p₀) * (2 - ξ) * (p₀ * (P.a₁ - P.a₀) - ξ * (P.b₀ - P.a₀)) / (2 * p₀) := by
  have hA : 0 < P.a₁ - P.a₀ := by linarith
  have hB : 0 < P.b₀ - P.a₀ := by linarith
  have hp0 : 0 ≤ p₀ := by
    by_contra h
    have : p₀ * (P.a₁ - P.a₀) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_le.mp h).le hA.le
    nlinarith [mul_pos hξ0 hB]
  unfold VI_ND costNoDisclosure
  rw [vi2_value P hab₀ hab₁ ha₀ hnest_a hnest_b hlt ξ hξ0 hξ p₀ hp₁ hl,
    vi2_K_low P hab₀ hab₁ ha₀ hnest_a hnest_b hlt ξ hξ0 hξ p₀ ⟨hp0, hp₁⟩ hl]
  ring

lemma vi2_VI_FD (ξ : ℝ) (hξ0 : 0 < ξ) (hξ : ξ * (P.b₀ - P.a₀) ≤ P.a₁ - P.a₀)
    (p₀ : ℝ) (hp₁ : p₀ ≤ 1) (hl : ξ * (P.b₀ - P.a₀) ≤ p₀ * (P.a₁ - P.a₀)) :
    VI_FD P ξ p₀ =
      (1 - p₀) * (ξ * ((P.a₁ - P.a₀) * (1 - ξ) + (P.b₀ - P.b₁) * (2 - ξ))) / 2 := by
  unfold VI_FD costFullDisclosure
  rw [vi2_value P hab₀ hab₁ ha₀ hnest_a hnest_b hlt ξ hξ0 hξ p₀ hp₁ hl,
    vi2_K_zero P hab₀ hab₁ ha₀ hnest_a hnest_b hlt ξ hξ0 hξ,
    vi2_K_low P hab₀ hab₁ ha₀ hnest_a hnest_b hlt ξ hξ0 hξ 1 ⟨zero_le_one, le_refl _⟩
      (by linarith)]
  unfold vi2_L
  ring

end vi2final

theorem vi2_theorem_2
    (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (hlt : P.a₀ < P.a₁) :
    (∀ ξ : ℝ, 0 < ξ → ξ ≤ τlow P 1 →
        StrictMonoOn (fun p₀ => VI_ND P ξ p₀) (Set.Icc (pHat P ξ) (p₀star P ξ)) ∧
        StrictAntiOn (fun p₀ => VI_ND P ξ p₀) (Set.Icc (p₀star P ξ) 1)) ∧
    (∀ p₀ : ℝ, 0 < p₀ → p₀ < 1 →
        StrictAntiOn (fun ξ => VI_ND P ξ p₀) (Set.Ioc 0 (τlow P p₀))) ∧
    (∀ ξ : ℝ, 0 < ξ → ξ ≤ τlow P 1 →
        StrictAntiOn (fun p₀ => VI_FD P ξ p₀) (Set.Icc (pHat P ξ) 1)) ∧
    (∀ p₀ : ℝ, 0 < p₀ → p₀ < 1 →
        StrictMonoOn (fun ξ => VI_FD P ξ p₀) (Set.Ioc 0 (τlow P p₀) ∩ Set.Iic (ξstar P)) ∧
        StrictAntiOn (fun ξ => VI_FD P ξ p₀) (Set.Ioc 0 (τlow P p₀) ∩ Set.Ici (ξstar P))) := by
  have hA : 0 < P.a₁ - P.a₀ := by linarith
  have hB : 0 < P.b₀ - P.a₀ := by linarith
  have hD : 0 ≤ P.b₀ - P.b₁ := by linarith
  set A := P.a₁ - P.a₀ with hAdef
  set B := P.b₀ - P.a₀ with hBdef
  set D := P.b₀ - P.b₁ with hDdef
  have ND := vi2_VI_ND P hab₀ hab₁ ha₀ hnest_a hnest_b hlt
  have FD := vi2_VI_FD P hab₀ hab₁ ha₀ hnest_a hnest_b hlt
  -- conversions
  have hτ1 : ∀ ξ, ξ ≤ τlow P 1 → ξ * B ≤ A := by
    intro ξ h; unfold τlow at h; rw [one_mul, le_div_iff₀ hB] at h; exact h
  have hτp : ∀ ξ p, ξ ≤ τlow P p → ξ * B ≤ p * A := by
    intro ξ p h; unfold τlow at h; rwa [le_div_iff₀ hB] at h
  have hph : ∀ ξ p, pHat P ξ ≤ p → ξ * B ≤ p * A := by
    intro ξ p h; unfold pHat at h; rwa [div_le_iff₀ hA] at h
  have hph0 : ∀ ξ, 0 < ξ → 0 < pHat P ξ := by
    intro ξ h; unfold pHat; positivity
  refine ⟨fun ξ hξ0 hξ => ?_, fun p₀ hp0 hp1 => ?_, fun ξ hξ0 hξ => ?_, fun p₀ hp0 hp1 => ?_⟩
  · have hξB := hτ1 ξ hξ
    have hs : p₀star P ξ ^ 2 = ξ * B / A := by
      unfold p₀star; rw [Real.sq_sqrt (by positivity)]
    have hs0 : 0 ≤ p₀star P ξ := Real.sqrt_nonneg _
    have hsA : p₀star P ξ ^ 2 * A = ξ * B := by rw [hs]; field_simp
    have hs1 : p₀star P ξ ≤ 1 := by
      unfold p₀star
      rw [Real.sqrt_le_one]
      rw [div_le_one hA]; exact hξB
    -- VI_ND = (2-ξ)/2 * (A + ξB - (pA + ξB/p))
    have form : ∀ p, 0 < p → p ≤ 1 → ξ * B ≤ p * A →
        VI_ND P ξ p = (2 - ξ) / 2 * (A + ξ * B - (p * A + ξ * B / p)) := by
      intro p hp hp1 hl
      rw [ND ξ hξ0 hξB p hp1 hl]
      field_simp; ring
    constructor
    · intro x hx y hy hxy
      have hx0 : 0 < x := lt_of_lt_of_le (hph0 ξ hξ0) hx.1
      have hy0 : 0 < y := by linarith
      have hlx := hph ξ x hx.1
      have hly := hph ξ y (by linarith [hx.1])
      simp only
      rw [form x hx0 (by linarith [hx.2]) hlx, form y hy0 (by linarith [hy.2]) hly]
      have hxyA : x * y * A < ξ * B := by
        have : x * y < p₀star P ξ ^ 2 := by nlinarith [hy.2]
        rw [← hsA]; exact mul_lt_mul_of_pos_right this hA
      have key : (y - x) * A < ξ * B / x - ξ * B / y := by
        rw [div_sub_div _ _ hx0.ne' hy0.ne', lt_div_iff₀ (mul_pos hx0 hy0)]
        nlinarith
      have : 0 < 2 - ξ := by have := vi2_xi_lt_one P hab₀ hab₁ ha₀ hnest_a hnest_b hlt ξ hξB; linarith
      apply mul_lt_mul_of_pos_left _ (by positivity)
      linarith
    · intro x hx y hy hxy
      have hx0 : 0 < x := by
        rcases eq_or_lt_of_le hs0 with h | h
        · -- p₀star = 0 impossible
          exfalso
          rw [← h] at hsA; nlinarith [mul_pos hξ0 hB]
        · linarith [hx.1]
      have hy0 : 0 < y := by linarith
      have hlx : ξ * B ≤ x * A := by
        have : p₀star P ξ ^ 2 ≤ x := by nlinarith [hx.1, hx.2]
        nlinarith
      have hly : ξ * B ≤ y * A := by nlinarith
      simp only
      rw [form x hx0 (by linarith [hx.2, hy.2]) hlx, form y hy0 hy.2 hly]
      have hxyA : ξ * B < x * y * A := by
        have : p₀star P ξ ^ 2 < x * y := by nlinarith [hx.1]
        rw [← hsA]; exact mul_lt_mul_of_pos_right this hA
      have key : ξ * B / x - ξ * B / y < (y - x) * A := by
        rw [div_sub_div _ _ hx0.ne' hy0.ne', div_lt_iff₀ (mul_pos hx0 hy0)]
        nlinarith
      have : 0 < 2 - ξ := by have := vi2_xi_lt_one P hab₀ hab₁ ha₀ hnest_a hnest_b hlt ξ hξB; linarith
      apply mul_lt_mul_of_pos_left _ (by positivity)
      linarith
  · intro x hx y hy hxy
    have hlx := hτp x p₀ hx.2
    have hly := hτp y p₀ hy.2
    have hxB : x * B ≤ A := by nlinarith [hx.1]
    have hyB : y * B ≤ A := by nlinarith [hy.1]
    simp only
    rw [ND x hx.1 hxB p₀ hp1.le hlx, ND y hy.1 hyB p₀ hp1.le hly]
    have hy1 := vi2_xi_lt_one P hab₀ hab₁ ha₀ hnest_a hnest_b hlt y hyB
    have k : (2 - y) * (p₀ * A - y * B) < (2 - x) * (p₀ * A - x * B) := by
      have h1 : 0 ≤ p₀ * A - y * B := by linarith
      have h2 : 0 < (y - x) * B := mul_pos (by linarith) hB
      nlinarith
    have : 0 < 1 - p₀ := by linarith
    rw [div_lt_div_iff_of_pos_right (by positivity)]
    rw [mul_assoc, mul_assoc]
    exact mul_lt_mul_of_pos_left k this
  · have hξB := hτ1 ξ hξ
    have hξ1 := vi2_xi_lt_one P hab₀ hab₁ ha₀ hnest_a hnest_b hlt ξ hξB
    intro x hx y hy hxy
    simp only
    rw [FD ξ hξ0 hξB x (by linarith [hy.2]) (hph ξ x hx.1),
      FD ξ hξ0 hξB y hy.2 (hph ξ y (by linarith [hx.1]))]
    have hC : 0 < ξ * (A * (1 - ξ) + D * (2 - ξ)) := by
      apply mul_pos hξ0
      have := mul_pos hA (show 0 < 1 - ξ by linarith)
      have := mul_nonneg hD (show 0 ≤ 2 - ξ by linarith)
      linarith
    nlinarith
  · have hst : ξstar P * (2 * (D + A)) = A + 2 * D := by
      unfold ξstar
      have : D + A ≠ 0 := by positivity
      rw [show P.b₀ - P.b₁ + P.a₁ - P.a₀ = D + A by ring]
      field_simp; ring
    have hDA : 0 < D + A := by positivity
    have conv : ∀ x, x ∈ Set.Ioc 0 (τlow P p₀) → VI_FD P x p₀ =
        (1 - p₀) * (x * (A * (1 - x) + D * (2 - x))) / 2 := by
      intro x hx
      have hlx := hτp x p₀ hx.2
      exact FD x hx.1 (by nlinarith) p₀ hp1.le hlx
    have h1p : 0 < 1 - p₀ := by linarith
    constructor
    · intro x hx y hy hxy
      simp only
      rw [conv x hx.1, conv y hy.1]
      have hxy2 : (x + y) * (D + A) < A + 2 * D := by
        have : x + y < 2 * ξstar P := by linarith [show y ≤ ξstar P from hy.2]
        nlinarith
      have k : x * (A * (1 - x) + D * (2 - x)) < y * (A * (1 - y) + D * (2 - y)) := by
        nlinarith
      rw [div_lt_div_iff_of_pos_right (by norm_num)]
      exact mul_lt_mul_of_pos_left k h1p
    · intro x hx y hy hxy
      simp only
      rw [conv x hx.1, conv y hy.1]
      have hxy2 : A + 2 * D < (x + y) * (D + A) := by
        have : 2 * ξstar P < x + y := by linarith [show ξstar P ≤ x from hx.2]
        nlinarith
      have k : y * (A * (1 - y) + D * (2 - y)) < x * (A * (1 - x) + D * (2 - x)) := by
        nlinarith
      rw [div_lt_div_iff_of_pos_right (by norm_num)]
      exact mul_lt_mul_of_pos_left k h1p

theorem solution
    (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (hlt : P.a₀ < P.a₁) :
    (∀ ξ : ℝ, 0 < ξ → ξ ≤ τlow P 1 →
        StrictMonoOn (fun p₀ => VI_ND P ξ p₀) (Set.Icc (pHat P ξ) (p₀star P ξ)) ∧
        StrictAntiOn (fun p₀ => VI_ND P ξ p₀) (Set.Icc (p₀star P ξ) 1)) ∧
    (∀ p₀ : ℝ, 0 < p₀ → p₀ < 1 →
        StrictAntiOn (fun ξ => VI_ND P ξ p₀) (Set.Ioc 0 (τlow P p₀))) ∧
    (∀ ξ : ℝ, 0 < ξ → ξ ≤ τlow P 1 →
        StrictAntiOn (fun p₀ => VI_FD P ξ p₀) (Set.Icc (pHat P ξ) 1)) ∧
    (∀ p₀ : ℝ, 0 < p₀ → p₀ < 1 →
        StrictMonoOn (fun ξ => VI_FD P ξ p₀) (Set.Ioc 0 (τlow P p₀) ∩ Set.Iic (ξstar P)) ∧
        StrictAntiOn (fun ξ => VI_FD P ξ p₀) (Set.Ioc 0 (τlow P p₀) ∩ Set.Ici (ξstar P))) :=
  vi2_theorem_2 P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b hlt
