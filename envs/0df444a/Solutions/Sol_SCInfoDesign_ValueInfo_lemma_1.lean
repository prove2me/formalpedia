-- Prove2me | solution 1 for SCInfoDesign.ValueInfo.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T18:58:13.543921+00:00
-- url     : https://prove2.me/submissions/a51b7bd4-258c-44b9-a32a-f6ab3ae0b502

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

open BiconvexProg.BranchBound

lemma vi2_uniq_all (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀)
    (ha₁ : 0 ≤ P.a₁) (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    ∀ Q, IsOptimalQuantity P ξ p Q ↔ Q = prefQ P ξ p := by
  obtain ⟨h1, h2', h3⟩ := vi2_prop1 P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1 p hp
  have key : ∃ q, ∀ Q, IsOptimalQuantity P ξ p Q ↔ Q = q := by
    by_cases c1 : τup P p ≤ ξ
    · exact ⟨_, h1 c1⟩
    by_cases c2 : τlow P p ≤ ξ
    · exact ⟨_, h2' c2 (le_of_lt (not_le.mp c1))⟩
    exact ⟨_, h3 (le_of_lt (not_le.mp c2))⟩
  obtain ⟨q, hq⟩ := key
  have hset : {Q | IsOptimalQuantity P ξ p Q} = {q} := Set.ext fun Q => hq Q
  have : prefQ P ξ p = q := by
    show sSup {Q | IsOptimalQuantity P ξ p Q} = q
    rw [hset, csSup_singleton]
  rw [this]; exact hq

lemma vi2_K_nonneg (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ξ : ℝ)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) : 0 ≤ K P ξ p := by
  obtain ⟨hp0, hp1⟩ := hp
  have gnn : ∀ a b Q : ℝ, a < b → 0 ≤ vi2_gc a b Q := by
    intro a b Q hab
    unfold vi2_gc
    split_ifs with h1 h2
    · linarith
    · have : 0 < b - a := by linarith
      positivity
    · rfl
  unfold K retailerCost
  rw [vi2_mean_pos _ _ _ hab₀, vi2_mean_pos _ _ _ hab₁]
  have := gnn P.a₀ P.b₀ (prefQ P ξ p) hab₀
  have := gnn P.a₁ P.b₁ (prefQ P ξ p) hab₁
  have : 0 ≤ 1 - p := by linarith
  positivity

def vi2_Split (x : ℝ) (n : ℕ) (w q : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, q i ∈ Set.Icc (0:ℝ) 1) ∧ ∑ i, w i * q i = x

def vi2_A (P : Params) (ξ x : ℝ) : Set ℝ :=
  {v | ∃ (n : ℕ) (w q : Fin n → ℝ), vi2_Split x n w q ∧ v = ∑ i, w i * K P ξ (q i)}

noncomputable def vi2_h (P : Params) (ξ x : ℝ) : ℝ := sInf (vi2_A P ξ x)

lemma vi2_A_nonneg (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ξ : ℝ)
    (x v : ℝ) (hv : v ∈ vi2_A P ξ x) : 0 ≤ v := by
  obtain ⟨n, w, q, ⟨hw, -, hq, -⟩, rfl⟩ := hv
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (vi2_K_nonneg P hab₀ hab₁ ξ _ (hq i))

lemma vi2_A_trivial (P : Params) (ξ : ℝ) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    K P ξ x ∈ vi2_A P ξ x :=
  ⟨1, fun _ => 1, fun _ => x, ⟨fun _ => zero_le_one, by simp, fun _ => hx, by simp⟩, by simp⟩

lemma vi2_h_le_K (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ξ : ℝ)
    (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) : vi2_h P ξ x ≤ K P ξ x :=
  csInf_le ⟨0, fun v hv => vi2_A_nonneg P hab₀ hab₁ ξ x v hv⟩ (vi2_A_trivial P ξ x hx)

lemma vi2_A_comb (P : Params) (ξ : ℝ) (x y a b u v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hu : u ∈ vi2_A P ξ x) (hv : v ∈ vi2_A P ξ y) :
    a * u + b * v ∈ vi2_A P ξ (a * x + b * y) := by
  obtain ⟨n, w, q, ⟨hw, hw1, hq, hwq⟩, rfl⟩ := hu
  obtain ⟨m, w', q', ⟨hw', hw1', hq', hwq'⟩, rfl⟩ := hv
  refine ⟨n + m, Fin.append (fun i => a * w i) (fun j => b * w' j), Fin.append q q',
    ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]; exact mul_nonneg ha (hw i)
    · simp only [Fin.append_right]; exact mul_nonneg hb (hw' j)
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hw1, hw1']; linarith
  · intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]; exact hq i
    · simp only [Fin.append_right]; exact hq' j
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hwq, hwq']
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum]

lemma vi2_h_convex (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ξ : ℝ) :
    ConvexOn ℝ (Set.Icc (0:ℝ) 1) (vi2_h P ξ) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha0 hb0 hab
  simp only [smul_eq_mul]
  have bddA : ∀ z, BddBelow (vi2_A P ξ z) :=
    fun z => ⟨0, fun v hv => vi2_A_nonneg P hab₀ hab₁ ξ z v hv⟩
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨u, hu, hu'⟩ := exists_lt_of_csInf_lt ⟨_, vi2_A_trivial P ξ x hx⟩
    (lt_add_of_pos_right (vi2_h P ξ x) hε)
  obtain ⟨v, hv, hv'⟩ := exists_lt_of_csInf_lt ⟨_, vi2_A_trivial P ξ y hy⟩
    (lt_add_of_pos_right (vi2_h P ξ y) hε)
  have hmem := vi2_A_comb P ξ x y a b u v ha0 hb0 hab hu hv
  have h1 : vi2_h P ξ (a * x + b * y) ≤ a * u + b * v := csInf_le (bddA _) hmem
  have h2 : a * u ≤ a * (vi2_h P ξ x + ε) := mul_le_mul_of_nonneg_left hu'.le ha0
  have h3 : b * v ≤ b * (vi2_h P ξ y + ε) := mul_le_mul_of_nonneg_left hv'.le hb0
  rcases eq_or_lt_of_le ha0 with ha' | ha'
  · have h3' : b * v < b * (vi2_h P ξ y + ε) := mul_lt_mul_of_pos_left hv' (by linarith)
    nlinarith
  · have h2' : a * u < a * (vi2_h P ξ x + ε) := mul_lt_mul_of_pos_left hu' ha'
    nlinarith

theorem vi2_B2
    (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0 : ℝ) 1) :
    optimalCost P ξ p₀ =
      BiconvexProg.BranchBound.convexEnvelope (Set.Icc (0 : ℝ) 1) (K P ξ) p₀ := by
  obtain ⟨hp0, hp1⟩ := hp₀
  have uniq := vi2_uniq_all P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1
  have hG_bdd : BddAbove {r : ℝ | ∃ g : ℝ → ℝ, ConvexOn ℝ (Set.Icc (0:ℝ) 1) g ∧
      (∀ w ∈ Set.Icc (0:ℝ) 1, g w ≤ K P ξ w) ∧ r = g p₀} := by
    refine ⟨K P ξ p₀, ?_⟩
    rintro r ⟨g, -, hg, rfl⟩
    exact hg p₀ ⟨hp0, hp1⟩
  have hG_ne : Set.Nonempty {r : ℝ | ∃ g : ℝ → ℝ, ConvexOn ℝ (Set.Icc (0:ℝ) 1) g ∧
      (∀ w ∈ Set.Icc (0:ℝ) 1, g w ≤ K P ξ w) ∧ r = g p₀} :=
    ⟨0, fun _ => 0, convexOn_const 0 (convex_Icc 0 1),
      fun w hw => vi2_K_nonneg P hab₀ hab₁ ξ w hw, rfl⟩
  have hBR : IsBestResponseProfile P ξ (prefQ P ξ) := fun p hp => (uniq p hp _).2 rfl
  have hglb : IsGLB {c : ℝ | ∃ (n : ℕ) (π : Fin 2 → Fin n → ℝ) (Qs : ℝ → ℝ),
      IsPolicy π ∧ IsBestResponseProfile P ξ Qs ∧ c = expectedCost P p₀ π Qs}
      (convexEnvelope (Set.Icc (0:ℝ) 1) (K P ξ) p₀) := by
    constructor
    · rintro c ⟨n, π, Qs, hπ, hQs, rfl⟩
      unfold convexEnvelope
      apply csSup_le hG_ne
      rintro r ⟨g, hg, hgK, rfl⟩
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
          have a1 : 0 ≤ p₀ * π 0 m := mul_nonneg hp0 (hπ.1 0 m)
          have a2 : 0 ≤ (1 - p₀) * π 1 m := mul_nonneg (by linarith) (hπ.1 1 m)
          unfold msgProb at h
          rw [zero_mul]; linarith
        · field_simp
      have hqI : ∀ m, q m ∈ Set.Icc (0:ℝ) 1 := by
        intro m
        simp only [hq_def, posterior, msgProb]
        have a1 : 0 ≤ p₀ * π 0 m := mul_nonneg hp0 (hπ.1 0 m)
        have a2 : 0 ≤ (1 - p₀) * π 1 m := mul_nonneg (by linarith) (hπ.1 1 m)
        refine ⟨div_nonneg a1 (by linarith), ?_⟩
        rcases eq_or_lt_of_le (add_nonneg a1 a2) with h | h
        · rw [← h, div_zero]; norm_num
        · rw [div_le_one h]; linarith
      have hsum : ∑ m, w m * q m = p₀ := by
        simp_rw [hwq]; rw [← Finset.mul_sum, hπ.2 0, mul_one]
      have hJ := hg.map_sum_le (t := Finset.univ) (w := w) (p := q)
        (fun m _ => hwnn m) hw1 (fun m _ => hqI m)
      simp only [smul_eq_mul] at hJ
      rw [hsum] at hJ
      refine le_trans hJ ?_
      unfold expectedCost
      apply Finset.sum_le_sum
      intro m _
      have hQ : Qs (q m) = prefQ P ξ (q m) := (uniq (q m) (hqI m) _).1 (hQs (q m) (hqI m))
      show w m * g (q m) ≤ w m * retailerCost P (q m) (Qs (q m))
      rw [hQ]
      exact mul_le_mul_of_nonneg_left (hgK _ (hqI m)) (hwnn m)
    · intro c hc
      have h1 : c ≤ vi2_h P ξ p₀ := by
        apply le_csInf ⟨_, vi2_A_trivial P ξ p₀ ⟨hp0, hp1⟩⟩
        rintro v ⟨n, w, q, ⟨hw, hw1, hq, hwq⟩, rfl⟩
        obtain ⟨π, hπ, hcost⟩ := vi2_realize P ξ p₀ ⟨hp0, hp1⟩ n w q hw hw1 hq hwq
        rw [← hcost]
        exact hc ⟨n, π, prefQ P ξ, hπ, hBR, rfl⟩
      refine le_trans h1 ?_
      unfold convexEnvelope
      apply le_csSup hG_bdd
      exact ⟨vi2_h P ξ, vi2_h_convex P hab₀ hab₁ ξ, fun w hw => vi2_h_le_K P hab₀ hab₁ ξ w hw, rfl⟩
  have hne : Set.Nonempty {c : ℝ | ∃ (n : ℕ) (π : Fin 2 → Fin n → ℝ) (Qs : ℝ → ℝ),
      IsPolicy π ∧ IsBestResponseProfile P ξ Qs ∧ c = expectedCost P p₀ π Qs} := by
    obtain ⟨π, hπ, _⟩ := vi2_realize P ξ p₀ ⟨hp0, hp1⟩ 1 (fun _ => 1) (fun _ => p₀)
      (fun _ => zero_le_one) (by simp) (fun _ => ⟨hp0, hp1⟩) (by simp)
    exact ⟨_, 1, π, prefQ P ξ, hπ, hBR, rfl⟩
  exact hglb.csInf_eq hne


lemma vi2_gc_hi (a b Q : ℝ) (hab : a < b) (h : b ≤ Q) : vi2_gc a b Q = 0 := by
  unfold vi2_gc
  rw [if_neg (by linarith)]
  by_cases h2 : Q ≤ b
  · rw [if_pos h2, show Q = b by linarith]; simp
  · rw [if_neg h2]

noncomputable def vi2_K1 (P : Params) (ξ p : ℝ) : ℝ :=
  vi2_L P ξ p + (1 - p) * (ξ * (P.b₀ - P.a₀) - p * (P.a₁ - P.a₀)) *
    ((P.a₁ - P.a₀) * (1 - ξ) + (P.b₀ - P.b₁) * (2 - ξ)) /
    (2 * ((1 - p) * (P.b₀ - P.a₀) + p * (P.b₁ - P.a₁)))

lemma vi2_inv_conv (a b U V : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hU : 0 < U) (hV : 0 < V) : 1 / (a * U + b * V) ≤ a / U + b / V := by
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hW : 0 < a * U + (1 - a) * V := by
    rcases le_total U V with h | h
    · nlinarith
    · nlinarith
  rw [div_add_div _ _ hU.ne' hV.ne', div_le_div_iff₀ hW (mul_pos hU hV)]
  nlinarith [sq_nonneg (U - V), mul_nonneg ha hb]

section vi2l1
variable (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀)
    (ha₁ : 0 ≤ P.a₁) (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)

include hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b

lemma vi2_K_eq (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (q : ℝ)
    (h : ∀ Q, IsOptimalQuantity P ξ p Q ↔ Q = q) : K P ξ p = retailerCost P p q := by
  have := (vi2_uniq_all P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1 p hp q).1 ((h q).2 rfl)
  unfold K; rw [← this]

lemma vi2_K_mid' (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1)
    (hl : p * (P.a₁ - P.a₀) ≤ ξ * (P.b₀ - P.a₀))
    (hu : ξ * (P.b₀ - P.a₀) ≤ (P.b₀ - P.a₀) - p * (P.b₀ - P.b₁)) :
    K P ξ p = vi2_K1 P ξ p := by
  obtain ⟨hN, h1, h2⟩ := vi2_mid P hab₀ hab₁ ha₀ hnest_a hnest_b ξ hξ0 hξ1 p hp hl hu
  rw [vi2_K_eq P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1 p hp _ h1, h2]
  rfl

lemma vi2_K_low' (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1)
    (hl : ξ * (P.b₀ - P.a₀) ≤ p * (P.a₁ - P.a₀)) :
    K P ξ p =
      vi2_L P ξ p + (1 - p) * (2 - ξ) * (p * (P.a₁ - P.a₀) - ξ * (P.b₀ - P.a₀)) / (2 * p) := by
  obtain ⟨h1, h2⟩ := vi2_low P hab₀ hab₁ ha₀ hnest_a hnest_b ξ hξ0 hξ1 p hp hl
  rw [vi2_K_eq P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1 p hp _ h1, h2]

lemma vi2_K_high (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1)
    (hτ : (1 - ξ) * (P.b₀ - P.a₀) ≤ p * (P.b₀ - P.b₁)) :
    K P ξ p = (P.b₀ - P.a₀) * (1 - ξ) ^ 2 / (2 * p) := by
  obtain ⟨hp0, hp1⟩ := hp
  have hB : 0 < P.b₀ - P.a₀ := by linarith
  have hpp : 0 < p := by
    rcases eq_or_lt_of_le hp0 with h | h
    · rw [← h] at hτ; nlinarith
    · exact h
  have h1 := (vi2_prop1 P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1 p ⟨hp0, hp1⟩).1 (by
    unfold τup
    have : p * (P.b₀ - P.b₁) / (P.b₀ - P.a₀) ≥ 1 - ξ := by rw [ge_iff_le, le_div_iff₀ hB]; exact hτ
    linarith)
  rw [vi2_K_eq P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1 p ⟨hp0, hp1⟩ _ h1]
  set t := (P.b₀ - P.a₀) * (1 - ξ) / p with ht_def
  have ht : t * p = (P.b₀ - P.a₀) * (1 - ξ) := div_mul_cancel₀ _ hpp.ne'
  have htpos : 0 < t := by have : 0 < 1 - ξ := by linarith
                           positivity
  have hthi : t ≤ P.b₀ - P.b₁ := by nlinarith
  unfold retailerCost
  rw [vi2_mean_pos _ _ _ hab₀, vi2_mean_pos _ _ _ hab₁,
    vi2_gc_mid _ _ _ hab₀ (by nlinarith) (by linarith), vi2_gc_hi _ _ _ hab₁ (by linarith)]
  rw [ht_def]
  field_simp
  ring

lemma vi2_K_zero' (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    K P ξ 0 = vi2_L P ξ 0 + ξ * ((P.a₁ - P.a₀) * (1 - ξ) + (P.b₀ - P.b₁) * (2 - ξ)) / 2 := by
  have hB : 0 < P.b₀ - P.a₀ := by linarith
  rw [vi2_K_mid' P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1 0 ⟨le_refl _, zero_le_one⟩
    (by nlinarith) (by nlinarith)]
  unfold vi2_K1 vi2_L
  have hB' := hB.ne'
  simp only [sub_zero, zero_mul, add_zero, one_mul]
  field_simp

lemma vi2_K_one' (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) : K P ξ 1 = vi2_L P ξ 1 := by
  have hB : 0 < P.b₀ - P.a₀ := by linarith
  rcases le_total (ξ * (P.b₀ - P.a₀)) (1 * (P.a₁ - P.a₀)) with h | h
  · rw [vi2_K_low' P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1 1 ⟨zero_le_one, le_refl _⟩ h]
    simp
  rcases le_total (ξ * (P.b₀ - P.a₀)) ((P.b₀ - P.a₀) - 1 * (P.b₀ - P.b₁)) with h' | h'
  · rw [vi2_K_mid' P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1 1 ⟨zero_le_one, le_refl _⟩ h h']
    unfold vi2_K1; simp
  · rw [vi2_K_high P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1 1 ⟨zero_le_one, le_refl _⟩
      (by linarith)]
    unfold vi2_L; field_simp; ring

lemma vi2_K1_convex (ξ : ℝ) (hξ1 : ξ < 1)
    (hξE : ξ * (P.b₀ - P.a₀ - P.b₁ + P.a₁) ≤ P.a₁ - P.a₀)
    (hEpos : 0 < P.b₀ - P.a₀ - P.b₁ + P.a₁) :
    ConvexOn ℝ (Set.Icc (0:ℝ) 1) (vi2_K1 P ξ) := by
  have hB : 0 < P.b₀ - P.a₀ := by linarith
  have hL1 : 0 < P.b₁ - P.a₁ := by linarith
  set E := P.b₀ - P.a₀ - P.b₁ + P.a₁ with hE
  have hE0 : 0 < E := hEpos
  set C := (P.a₁ - P.a₀) * (1 - ξ) + (P.b₀ - P.b₁) * (2 - ξ) with hC
  have hC0 : 0 ≤ C := by
    have := mul_nonneg (show 0 ≤ P.a₁ - P.a₀ by linarith) (show 0 ≤ 1 - ξ by linarith)
    have := mul_nonneg (show 0 ≤ P.b₀ - P.b₁ by linarith) (show 0 ≤ 2 - ξ by linarith)
    rw [hC]; linarith
  set M := C / 2 * ((P.b₀ - P.a₀) * ((P.a₁ - P.a₀) - E * ξ) * ((P.b₀ - P.a₀) - E) / E ^ 2)
    with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    apply mul_nonneg (by positivity)
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (mul_nonneg hB.le (by linarith)) (by rw [hE]; linarith)
  let N : ℝ → ℝ := fun w => (1 - w) * (P.b₀ - P.a₀) + w * (P.b₁ - P.a₁)
  have hNpos : ∀ w ∈ Set.Icc (0:ℝ) 1, 0 < N w := by
    intro w hw
    show 0 < (1 - w) * (P.b₀ - P.a₀) + w * (P.b₁ - P.a₁)
    rcases eq_or_lt_of_le hw.1 with h | h
    · rw [← h]; linarith
    · have := mul_pos h hL1
      have := mul_nonneg (show 0 ≤ 1 - w by linarith [hw.2]) hB.le
      linarith
  let aff : ℝ → ℝ := fun w => vi2_L P ξ w +
    C / 2 * (((P.a₁ - P.a₀) * E + (P.b₀ - P.a₀) * E * ξ - (P.a₁ - P.a₀) * (P.b₀ - P.a₀) -
      (P.a₁ - P.a₀) * E * w) / E ^ 2)
  have hdec : ∀ w ∈ Set.Icc (0:ℝ) 1, vi2_K1 P ξ w = aff w + M / N w := by
    intro w hw
    have hN := (hNpos w hw).ne'
    show _ = vi2_L P ξ w +
      C / 2 * (((P.a₁ - P.a₀) * E + (P.b₀ - P.a₀) * E * ξ - (P.a₁ - P.a₀) * (P.b₀ - P.a₀) -
        (P.a₁ - P.a₀) * E * w) / E ^ 2) + M / ((1 - w) * (P.b₀ - P.a₀) + w * (P.b₁ - P.a₁))
    have hN' : (1 - w) * (P.b₀ - P.a₀) + w * (P.b₁ - P.a₁) ≠ 0 := hN
    unfold vi2_K1
    rw [hM, hC, hE]
    have hE' : P.b₀ - P.a₀ - P.b₁ + P.a₁ ≠ 0 := hE0.ne'
    field_simp
    ring
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : a • x + b • y ∈ Set.Icc (0:ℝ) 1 := (convex_Icc 0 1) hx hy ha hb hab
  simp only [smul_eq_mul] at hz ⊢
  rw [hdec _ hz, hdec x hx, hdec y hy]
  have hNz : N (a * x + b * y) = a * N x + b * N y := by
    show (1 - (a * x + b * y)) * (P.b₀ - P.a₀) + (a * x + b * y) * (P.b₁ - P.a₁) =
      a * ((1 - x) * (P.b₀ - P.a₀) + x * (P.b₁ - P.a₁)) +
        b * ((1 - y) * (P.b₀ - P.a₀) + y * (P.b₁ - P.a₁))
    rw [show b = 1 - a by linarith]; ring
  have haff : aff (a * x + b * y) = a * aff x + b * aff y := by
    show vi2_L P ξ (a * x + b * y) + _ = a * (vi2_L P ξ x + _) + b * (vi2_L P ξ y + _)
    unfold vi2_L
    rw [show b = 1 - a by linarith]; ring
  have key := vi2_inv_conv a b (N x) (N y) ha hb hab (hNpos x hx) (hNpos y hy)
  have key2 : M / N (a * x + b * y) ≤ a * (M / N x) + b * (M / N y) := by
    rw [hNz]
    have := mul_le_mul_of_nonneg_left key hM0
    calc M / (a * N x + b * N y) = M * (1 / (a * N x + b * N y)) := by ring
      _ ≤ M * (a / N x + b / N y) := this
      _ = a * (M / N x) + b * (M / N y) := by ring
  rw [haff]
  linarith

lemma vi2_affine_convex (c0 c1 : ℝ) : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun w => c0 + c1 * w) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x _ y _ a b _ _ hab
  simp only [smul_eq_mul]
  rw [show b = 1 - a by linarith]
  apply le_of_eq; ring

omit hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b in
lemma vi2_env_le (f : ℝ → ℝ) (p v : ℝ) (hne : ∃ g : ℝ → ℝ, ConvexOn ℝ (Set.Icc (0:ℝ) 1) g ∧
      (∀ w ∈ Set.Icc (0:ℝ) 1, g w ≤ f w))
    (h : ∀ g : ℝ → ℝ, ConvexOn ℝ (Set.Icc (0:ℝ) 1) g → (∀ w ∈ Set.Icc (0:ℝ) 1, g w ≤ f w) →
      g p ≤ v) :
    BiconvexProg.BranchBound.convexEnvelope (Set.Icc (0 : ℝ) 1) f p ≤ v := by
  unfold convexEnvelope
  obtain ⟨g0, hg0, hg0f⟩ := hne
  apply csSup_le
  · exact ⟨g0 p, g0, hg0, hg0f, rfl⟩
  · rintro r ⟨g, hg, hgf, rfl⟩
    exact h g hg hgf

omit hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b in
lemma vi2_env_ge (f : ℝ → ℝ) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (g : ℝ → ℝ)
    (hg : ConvexOn ℝ (Set.Icc (0:ℝ) 1) g) (hgf : ∀ w ∈ Set.Icc (0:ℝ) 1, g w ≤ f w) :
    g p ≤ BiconvexProg.BranchBound.convexEnvelope (Set.Icc (0 : ℝ) 1) f p := by
  unfold convexEnvelope
  apply le_csSup
  · refine ⟨f p, ?_⟩
    rintro r ⟨g', -, hg', rfl⟩
    exact hg' p hp
  · exact ⟨g, hg, hgf, rfl⟩

theorem vi2_lemma_1 (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    ((P.a₁ - P.a₀) / (P.b₀ - P.a₀ - P.b₁ + P.a₁) ≤ ξ →
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        BiconvexProg.BranchBound.convexEnvelope (Set.Icc (0 : ℝ) 1) (K P ξ) p =
          p * K P ξ 1 + (1 - p) * K P ξ 0) ∧
    ((P.a₁ - P.a₀) / (P.b₀ - P.a₀) ≤ ξ → ξ ≤ (P.a₁ - P.a₀) / (P.b₀ - P.a₀ - P.b₁ + P.a₁) →
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        BiconvexProg.BranchBound.convexEnvelope (Set.Icc (0 : ℝ) 1) (K P ξ) p = K P ξ p) ∧
    (ξ ≤ (P.a₁ - P.a₀) / (P.b₀ - P.a₀) →
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        BiconvexProg.BranchBound.convexEnvelope (Set.Icc (0 : ℝ) 1) (K P ξ) p =
          if p ≤ pHat P ξ then K P ξ p
          else (K P ξ 1 - K P ξ (pHat P ξ)) / (1 - pHat P ξ) * (p - pHat P ξ) +
            K P ξ (pHat P ξ)) := by
  have hB : 0 < P.b₀ - P.a₀ := by linarith
  have hL1 : 0 < P.b₁ - P.a₁ := by linarith
  have hE0 : 0 ≤ P.b₀ - P.a₀ - P.b₁ + P.a₁ := by linarith
  have hEB : P.b₀ - P.a₀ - P.b₁ + P.a₁ ≤ P.b₀ - P.a₀ := by linarith
  have hKnn : ∃ g : ℝ → ℝ, ConvexOn ℝ (Set.Icc (0:ℝ) 1) g ∧
      (∀ w ∈ Set.Icc (0:ℝ) 1, g w ≤ K P ξ w) :=
    ⟨fun _ => 0, convexOn_const 0 (convex_Icc 0 1),
      fun w hw => vi2_K_nonneg P hab₀ hab₁ ξ w hw⟩
  have hC : 0 < (P.a₁ - P.a₀) * (1 - ξ) + (P.b₀ - P.b₁) * (2 - ξ) ∨
      (P.a₁ - P.a₀ = 0 ∧ P.b₀ - P.b₁ = 0) := by
    by_cases h : P.a₁ - P.a₀ = 0 ∧ P.b₀ - P.b₁ = 0
    · right; exact h
    · left
      rcases not_and_or.mp h with h | h
      · have := mul_pos (show 0 < P.a₁ - P.a₀ by
          rcases eq_or_lt_of_le (show 0 ≤ P.a₁ - P.a₀ by linarith) with e | e
          · exact absurd e.symm h
          · exact e) (show 0 < 1 - ξ by linarith)
        have := mul_nonneg (show 0 ≤ P.b₀ - P.b₁ by linarith) (show 0 ≤ 2 - ξ by linarith)
        linarith
      · have := mul_pos (show 0 < P.b₀ - P.b₁ by
          rcases eq_or_lt_of_le (show 0 ≤ P.b₀ - P.b₁ by linarith) with e | e
          · exact absurd e.symm h
          · exact e) (show 0 < 2 - ξ by linarith)
        have := mul_nonneg (show 0 ≤ P.a₁ - P.a₀ by linarith) (show 0 ≤ 1 - ξ by linarith)
        linarith
  have hC0 : 0 ≤ (P.a₁ - P.a₀) * (1 - ξ) + (P.b₀ - P.b₁) * (2 - ξ) := by
    rcases hC with h | ⟨h1, h2⟩
    · exact h.le
    · rw [h1, h2]; ring_nf; rfl
  have hNpos : ∀ w ∈ Set.Icc (0:ℝ) 1, 0 < (1 - w) * (P.b₀ - P.a₀) + w * (P.b₁ - P.a₁) := by
    intro w hw
    rcases eq_or_lt_of_le hw.1 with h | h
    · rw [← h]; linarith
    · have := mul_pos h hL1
      have := mul_nonneg (show 0 ≤ 1 - w by linarith [hw.2]) hB.le
      linarith
  have K0 := vi2_K_zero' P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1
  have K1e := vi2_K_one' P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1
  refine ⟨fun hξh p hp => ?_, fun hξl hξh p hp => ?_, fun hξl p hp => ?_⟩
  · -- chord regime
    have hξE : P.a₁ - P.a₀ ≤ ξ * (P.b₀ - P.a₀ - P.b₁ + P.a₁) := by
      rcases eq_or_lt_of_le hE0 with h | h
      · rw [← h]; linarith
      · rwa [div_le_iff₀ h] at hξh
    apply le_antisymm
    · apply vi2_env_le _ _ _ hKnn
      intro g hg hgK
      have := hg.2 (show (0:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨le_refl _, zero_le_one⟩)
        (show (1:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨zero_le_one, le_refl _⟩)
        (show 0 ≤ 1 - p by linarith [hp.2]) hp.1 (by ring)
      simp only [smul_eq_mul, mul_zero, mul_one, zero_add] at this
      have h0 := hgK 0 ⟨le_refl _, zero_le_one⟩
      have h1 := hgK 1 ⟨zero_le_one, le_refl _⟩
      have := mul_le_mul_of_nonneg_left h0 (show 0 ≤ 1 - p by linarith [hp.2])
      have := mul_le_mul_of_nonneg_left h1 hp.1
      linarith
    · have hc := vi2_affine_convex P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b (K P ξ 0)
        (K P ξ 1 - K P ξ 0)
      have := vi2_env_ge (K P ξ) p hp _ hc (by
        intro w hw
        show K P ξ 0 + (K P ξ 1 - K P ξ 0) * w ≤ K P ξ w
        rw [K0, K1e]
        by_cases hhigh : (1 - ξ) * (P.b₀ - P.a₀) ≤ w * (P.b₀ - P.b₁)
        · rw [vi2_K_high P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1 w hw hhigh]
          have hw0 : 0 < w := by
            rcases eq_or_lt_of_le hw.1 with h | h
            · rw [← h] at hhigh; nlinarith
            · exact h
          have : 0 ≤ (1 - w) * (1 - ξ) ^ 2 * ((P.b₀ - P.a₀) + w * (P.b₀ - P.a₀ - P.b₁ + P.a₁)) /
              (2 * w) := by
            apply div_nonneg _ (by positivity)
            apply mul_nonneg (mul_nonneg (by linarith [hw.2]) (sq_nonneg _))
            nlinarith [hw.1]
          have e : (P.b₀ - P.a₀) * (1 - ξ) ^ 2 / (2 * w) - (K P ξ 0 + (K P ξ 1 - K P ξ 0) * w) =
              (1 - w) * (1 - ξ) ^ 2 * ((P.b₀ - P.a₀) + w * (P.b₀ - P.a₀ - P.b₁ + P.a₁)) /
              (2 * w) := by
            rw [K0, K1e]; unfold vi2_L; field_simp; ring
          rw [K0, K1e] at e
          linarith
        · rw [vi2_K_mid' P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1 w hw (by nlinarith [hw.2])
            (by linarith)]
          have hN := hNpos w hw
          have : 0 ≤ (1 - w) * w * (ξ * (P.b₀ - P.a₀ - P.b₁ + P.a₁) - (P.a₁ - P.a₀)) *
              ((P.a₁ - P.a₀) * (1 - ξ) + (P.b₀ - P.b₁) * (2 - ξ)) /
              (2 * ((1 - w) * (P.b₀ - P.a₀) + w * (P.b₁ - P.a₁))) := by
            apply div_nonneg _ (by positivity)
            apply mul_nonneg (mul_nonneg (mul_nonneg (by linarith [hw.2]) hw.1) (by linarith)) hC0
          have e : vi2_K1 P ξ w - (vi2_L P ξ 0 +
              ξ * ((P.a₁ - P.a₀) * (1 - ξ) + (P.b₀ - P.b₁) * (2 - ξ)) / 2 +
              (vi2_L P ξ 1 - (vi2_L P ξ 0 +
                ξ * ((P.a₁ - P.a₀) * (1 - ξ) + (P.b₀ - P.b₁) * (2 - ξ)) / 2)) * w) =
              (1 - w) * w * (ξ * (P.b₀ - P.a₀ - P.b₁ + P.a₁) - (P.a₁ - P.a₀)) *
              ((P.a₁ - P.a₀) * (1 - ξ) + (P.b₀ - P.b₁) * (2 - ξ)) /
              (2 * ((1 - w) * (P.b₀ - P.a₀) + w * (P.b₁ - P.a₁))) := by
            unfold vi2_K1 vi2_L; field_simp; ring
          linarith)
      linarith
  · -- K convex regime
    have hE0' : 0 < P.b₀ - P.a₀ - P.b₁ + P.a₁ := by
      rcases eq_or_lt_of_le hE0 with h | h
      · rw [← h, div_zero] at hξh; linarith
      · exact h
    have hξE : ξ * (P.b₀ - P.a₀ - P.b₁ + P.a₁) ≤ P.a₁ - P.a₀ := by rwa [le_div_iff₀ hE0'] at hξh
    have hξB : P.a₁ - P.a₀ ≤ ξ * (P.b₀ - P.a₀) := by rwa [div_le_iff₀ hB] at hξl
    have hmid : ∀ w ∈ Set.Icc (0:ℝ) 1, K P ξ w = vi2_K1 P ξ w := by
      intro w hw
      apply vi2_K_mid' P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1 w hw
      · nlinarith [hw.2]
      · nlinarith [hw.2, hw.1]
    apply le_antisymm
    · apply vi2_env_le _ _ _ hKnn
      intro g _ hgK; exact hgK p hp
    · rw [hmid p hp]
      exact vi2_env_ge (K P ξ) p hp _
        (vi2_K1_convex P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ1 hξE hE0')
        (fun w hw => (hmid w hw).ge)
  · -- partial regime
    have hξB : ξ * (P.b₀ - P.a₀) ≤ P.a₁ - P.a₀ := by rwa [le_div_iff₀ hB] at hξl
    have hA : 0 < P.a₁ - P.a₀ := by nlinarith [mul_pos hξ0 hB]
    have hξE : ξ * (P.b₀ - P.a₀ - P.b₁ + P.a₁) ≤ P.a₁ - P.a₀ := by nlinarith
    -- K ≥ L everywhere
    have hKL : ∀ w ∈ Set.Icc (0:ℝ) 1, vi2_L P ξ w ≤ K P ξ w := by
      intro w hw
      obtain ⟨q, hq, hLq⟩ := vi2_uniq P hab₀ hab₁ ha₀ hnest_a hnest_b (by linarith) ξ hξ0 hξB w hw
      rw [vi2_K_eq P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1 w hw q hq]
      exact hLq
    have hLconv : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (vi2_L P ξ) := by
      have := vi2_affine_convex P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b (vi2_L P ξ 0)
        (vi2_L P ξ 1 - vi2_L P ξ 0)
      apply this.congr
      intro w _
      unfold vi2_L; ring
    have hph0 : 0 < pHat P ξ := by unfold pHat; positivity
    have hphA : pHat P ξ * (P.a₁ - P.a₀) = ξ * (P.b₀ - P.a₀) := by
      unfold pHat; field_simp
    split_ifs with hc
    · -- envelope = K
      have hl : p * (P.a₁ - P.a₀) ≤ ξ * (P.b₀ - P.a₀) := by
        rw [← hphA]; exact mul_le_mul_of_nonneg_right hc hA.le
      have hu : ∀ w ∈ Set.Icc (0:ℝ) 1, ξ * (P.b₀ - P.a₀) ≤ (P.b₀ - P.a₀) - w * (P.b₀ - P.b₁) := by
        intro w hw; nlinarith [hw.2]
      apply le_antisymm
      · apply vi2_env_le _ _ _ hKnn
        intro g _ hgK; exact hgK p hp
      · have hgconv := (vi2_K1_convex P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ1 hξE
          (by linarith)).sup hLconv
        have := vi2_env_ge (K P ξ) p hp _ hgconv (by
          intro w hw
          simp only [Pi.sup_apply]
          apply max_le _ (hKL w hw)
          by_cases hwl : w * (P.a₁ - P.a₀) ≤ ξ * (P.b₀ - P.a₀)
          · rw [vi2_K_mid' P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1 w hw hwl (hu w hw)]
          · have hN := hNpos w hw
            have : (1 - w) * (ξ * (P.b₀ - P.a₀) - w * (P.a₁ - P.a₀)) *
                ((P.a₁ - P.a₀) * (1 - ξ) + (P.b₀ - P.b₁) * (2 - ξ)) /
                (2 * ((1 - w) * (P.b₀ - P.a₀) + w * (P.b₁ - P.a₁))) ≤ 0 := by
              apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
              apply mul_nonpos_of_nonpos_of_nonneg _ hC0
              apply mul_nonpos_of_nonneg_of_nonpos (by linarith [hw.2])
              linarith
            have e : vi2_K1 P ξ w = vi2_L P ξ w + (1 - w) *
                (ξ * (P.b₀ - P.a₀) - w * (P.a₁ - P.a₀)) *
                ((P.a₁ - P.a₀) * (1 - ξ) + (P.b₀ - P.b₁) * (2 - ξ)) /
                (2 * ((1 - w) * (P.b₀ - P.a₀) + w * (P.b₁ - P.a₁))) := rfl
            linarith [hKL w hw])
        simp only [Pi.sup_apply] at this
        rw [vi2_K_mid' P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1 p hp hl (hu p hp)]
        exact le_trans (le_max_left _ _) this
    · -- chord from p̂ to 1
      have hc' : pHat P ξ < p := not_le.mp hc
      have hph1 : pHat P ξ < 1 := lt_of_lt_of_le hc' hp.2
      have hph1' : 1 - pHat P ξ ≠ 0 := by linarith
      have hphI : pHat P ξ ∈ Set.Icc (0:ℝ) 1 := ⟨hph0.le, hph1.le⟩
      have hKph : K P ξ (pHat P ξ) = vi2_L P ξ (pHat P ξ) := by
        rw [vi2_K_low' P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1 _ hphI (by rw [hphA])]
        rw [hphA]; simp
      have htarget : (K P ξ 1 - K P ξ (pHat P ξ)) / (1 - pHat P ξ) * (p - pHat P ξ) +
          K P ξ (pHat P ξ) = vi2_L P ξ p := by
        rw [K1e, hKph]; unfold vi2_L; field_simp; ring
      rw [htarget]
      apply le_antisymm
      · apply vi2_env_le _ _ _ hKnn
        intro g hg hgK
        set a := (1 - p) / (1 - pHat P ξ)
        set b := (p - pHat P ξ) / (1 - pHat P ξ)
        have ha : 0 ≤ a := div_nonneg (by linarith [hp.2]) (by linarith)
        have hb : 0 ≤ b := div_nonneg (by linarith) (by linarith)
        have hab : a + b = 1 := by
          simp only [a, b]; field_simp; ring
        have hpt : a * pHat P ξ + b * 1 = p := by
          simp only [a, b]; field_simp; ring
        have := hg.2 hphI (show (1:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨zero_le_one, le_refl _⟩) ha hb hab
        simp only [smul_eq_mul] at this
        rw [hpt] at this
        have h0 := mul_le_mul_of_nonneg_left (hgK _ hphI) ha
        have h1 := mul_le_mul_of_nonneg_left (hgK 1 ⟨zero_le_one, le_refl _⟩) hb
        rw [hKph] at h0
        rw [K1e] at h1
        have hL : a * vi2_L P ξ (pHat P ξ) + b * vi2_L P ξ 1 = vi2_L P ξ p := by
          rw [← hpt]; unfold vi2_L
          rw [show b = 1 - a by linarith]; ring
        linarith
      · exact vi2_env_ge (K P ξ) p hp _ hLconv hKL

end vi2l1

theorem solution
    (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    ((P.a₁ - P.a₀) / (P.b₀ - P.a₀ - P.b₁ + P.a₁) ≤ ξ →
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        BiconvexProg.BranchBound.convexEnvelope (Set.Icc (0 : ℝ) 1) (K P ξ) p =
          p * K P ξ 1 + (1 - p) * K P ξ 0) ∧
    ((P.a₁ - P.a₀) / (P.b₀ - P.a₀) ≤ ξ → ξ ≤ (P.a₁ - P.a₀) / (P.b₀ - P.a₀ - P.b₁ + P.a₁) →
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        BiconvexProg.BranchBound.convexEnvelope (Set.Icc (0 : ℝ) 1) (K P ξ) p = K P ξ p) ∧
    (ξ ≤ (P.a₁ - P.a₀) / (P.b₀ - P.a₀) →
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        BiconvexProg.BranchBound.convexEnvelope (Set.Icc (0 : ℝ) 1) (K P ξ) p =
          if p ≤ pHat P ξ then K P ξ p
          else (K P ξ 1 - K P ξ (pHat P ξ)) / (1 - pHat P ξ) * (p - pHat P ξ) +
            K P ξ (pHat P ξ)) :=
  vi2_lemma_1 P hab₀ hab₁ ha₀ ha₁ hnest_a hnest_b ξ hξ0 hξ1
