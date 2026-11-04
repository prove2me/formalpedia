-- Prove2me | solution 1 for SCInfoDesign.Intersecting.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T14:01:42.163199+00:00
-- url     : https://prove2.me/submissions/0a23146a-3694-4b35-a0ac-6ff34cd9f20a

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Intersecting_Setting

open SCInfoDesign.Intersecting

noncomputable def scid3_gc (a b Q : ℝ) : ℝ :=
  if Q ≤ a then (a + b) / 2 - Q else if Q ≤ b then (b - Q) ^ 2 / (2 * (b - a)) else 0

noncomputable def scid3_Fc (a b q : ℝ) : ℝ :=
  if q ≤ a then 0 else if q ≤ b then (q - a) / (b - a) else 1

lemma scid3_int_pos (a b Q : ℝ) (hab : a < b) :
    ∫ x in a..b, max (x - Q) 0 = (b - a) * scid3_gc a b Q := by
  have hba : (b - a) ≠ 0 := by linarith
  unfold scid3_gc
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

lemma scid3_mean_pos (a b Q : ℝ) (hab : a < b) :
    SCInfoDesign.Nested.uniformMean a b (fun d => max (d - Q) 0) = scid3_gc a b Q := by
  unfold SCInfoDesign.Nested.uniformMean
  rw [scid3_int_pos a b Q hab]
  field_simp [show b - a ≠ 0 by linarith]

lemma scid3_mean_supp (a b Q ξ : ℝ) (hab : a < b) :
    SCInfoDesign.Nested.uniformMean a b
      (fun d => ξ * max (d - Q) 0 + (1 - ξ) * max (Q - d) 0) =
      scid3_gc a b Q - (1 - ξ) * ((a + b) / 2 - Q) := by
  have hpt : (fun d => ξ * max (d - Q) 0 + (1 - ξ) * max (Q - d) 0) =
      fun d => max (d - Q) 0 - (1 - ξ) * (d - Q) := by
    funext d
    rcases le_total d Q with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have hc : Continuous fun x : ℝ => max (x - Q) 0 := by fun_prop
  unfold SCInfoDesign.Nested.uniformMean
  rw [hpt, intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
    (by apply Continuous.intervalIntegrable; fun_prop), scid3_int_pos a b Q hab,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    intervalIntegral.intervalIntegrable_id intervalIntegrable_const]
  simp [integral_id]
  field_simp [show b - a ≠ 0 by linarith]
  ring

lemma scid3_U (a b q Q : ℝ) (hab : a < b) :
    scid3_gc a b q - (1 - scid3_Fc a b q) * (Q - q) ≤ scid3_gc a b Q ∧
    (a < q → q < b → Q ≠ q →
      scid3_gc a b q - (1 - scid3_Fc a b q) * (Q - q) < scid3_gc a b Q) := by
  have hL : 0 < b - a := by linarith
  have hL' : b - a ≠ 0 := hL.ne'
  -- value of gc at Q
  have gQ : (Q ≤ a ∧ scid3_gc a b Q = (a + b) / 2 - Q) ∨
      (a < Q ∧ Q ≤ b ∧ scid3_gc a b Q = (b - Q) ^ 2 / (2 * (b - a))) ∨
      (b < Q ∧ scid3_gc a b Q = 0) := by
    unfold scid3_gc
    by_cases h1 : Q ≤ a
    · left; exact ⟨h1, by rw [if_pos h1]⟩
    · by_cases h2 : Q ≤ b
      · right; left; exact ⟨not_le.mp h1, h2, by rw [if_neg h1, if_pos h2]⟩
      · right; right; exact ⟨not_le.mp h2, by rw [if_neg h1, if_neg h2]⟩
  have gnn : 0 ≤ scid3_gc a b Q := by
    rcases gQ with ⟨h, e⟩ | ⟨h, h', e⟩ | ⟨h, e⟩ <;> rw [e]
    · linarith
    · positivity
  by_cases hq1 : q ≤ a
  · have e1 : scid3_gc a b q - (1 - scid3_Fc a b q) * (Q - q) = (a + b) / 2 - Q := by
      unfold scid3_gc scid3_Fc; rw [if_pos hq1, if_pos hq1]; ring
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
    have e1 : scid3_gc a b q - (1 - scid3_Fc a b q) * (Q - q) =
        (b - q) ^ 2 / (2 * (b - a)) - (b - q) / (b - a) * (Q - q) := by
      unfold scid3_gc scid3_Fc; rw [if_neg hq1, if_pos hq2, if_neg hq1, if_pos hq2]
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
  · have e1 : scid3_gc a b q - (1 - scid3_Fc a b q) * (Q - q) = 0 := by
      unfold scid3_gc scid3_Fc; rw [if_neg hq1, if_neg hq2, if_neg hq1, if_neg hq2]; ring
    rw [e1]
    exact ⟨gnn, fun _ h => absurd h (by linarith [not_le.mp hq2])⟩

lemma scid3_opt_iff (P : Params) (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (q : ℝ) (hq0 : 0 ≤ q)
    (hF : p * scid3_Fc P.a₀ P.b₀ q + (1 - p) * scid3_Fc P.a₁ P.b₁ q = P.ξ)
    (hstrict : (0 < 1 - p ∧ P.a₁ < q ∧ q < P.b₁) ∨ (0 < p ∧ P.a₀ < q ∧ q < P.b₀)) :
    ∀ Q, P.IsOptimalQuantity p Q ↔ Q = q := by
  obtain ⟨hp0, hp1⟩ := hp
  have h0 : P.a₀ < P.b₀ := by linarith
  have h1 : P.a₁ < P.b₁ := by linarith
  have hS : ∀ Q, P.supplierCost p Q =
      p * (scid3_gc P.a₀ P.b₀ Q - (1 - P.ξ) * ((P.a₀ + P.b₀) / 2 - Q)) +
      (1 - p) * (scid3_gc P.a₁ P.b₁ Q - (1 - P.ξ) * ((P.a₁ + P.b₁) / 2 - Q)) := by
    intro Q
    unfold Params.supplierCost
    rw [scid3_mean_supp _ _ _ _ h0, scid3_mean_supp _ _ _ _ h1]
  have hdiff : ∀ Q, P.supplierCost p Q - P.supplierCost p q =
      p * (scid3_gc P.a₀ P.b₀ Q - (scid3_gc P.a₀ P.b₀ q - (1 - scid3_Fc P.a₀ P.b₀ q) * (Q - q))) +
      (1 - p) * (scid3_gc P.a₁ P.b₁ Q -
        (scid3_gc P.a₁ P.b₁ q - (1 - scid3_Fc P.a₁ P.b₁ q) * (Q - q))) := by
    intro Q
    rw [hS, hS]
    linear_combination (Q - q) * hF
  have hge : ∀ Q, P.supplierCost p q ≤ P.supplierCost p Q := by
    intro Q
    have := hdiff Q
    have u0 := (scid3_U P.a₀ P.b₀ q Q h0).1
    have u1 := (scid3_U P.a₁ P.b₁ q Q h1).1
    have : 0 ≤ p * (scid3_gc P.a₀ P.b₀ Q -
        (scid3_gc P.a₀ P.b₀ q - (1 - scid3_Fc P.a₀ P.b₀ q) * (Q - q))) :=
      mul_nonneg hp0 (by linarith)
    have : 0 ≤ (1 - p) * (scid3_gc P.a₁ P.b₁ Q -
        (scid3_gc P.a₁ P.b₁ q - (1 - scid3_Fc P.a₁ P.b₁ q) * (Q - q))) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hgt : ∀ Q, Q ≠ q → P.supplierCost p q < P.supplierCost p Q := by
    intro Q hne
    have := hdiff Q
    have u0 := scid3_U P.a₀ P.b₀ q Q h0
    have u1 := scid3_U P.a₁ P.b₁ q Q h1
    have n0 : 0 ≤ p * (scid3_gc P.a₀ P.b₀ Q -
        (scid3_gc P.a₀ P.b₀ q - (1 - scid3_Fc P.a₀ P.b₀ q) * (Q - q))) :=
      mul_nonneg hp0 (by linarith [u0.1])
    have n1 : 0 ≤ (1 - p) * (scid3_gc P.a₁ P.b₁ Q -
        (scid3_gc P.a₁ P.b₁ q - (1 - scid3_Fc P.a₁ P.b₁ q) * (Q - q))) :=
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

lemma scid3_Fc_lo (a b q : ℝ) (h : q ≤ a) : scid3_Fc a b q = 0 := by
  unfold scid3_Fc; rw [if_pos h]

lemma scid3_Fc_mid (a b q : ℝ) (hab : a < b) (h1 : a ≤ q) (h2 : q ≤ b) :
    scid3_Fc a b q = (q - a) / (b - a) := by
  unfold scid3_Fc
  by_cases h : q ≤ a
  · rw [if_pos h, show q = a by linarith]; simp
  · rw [if_neg h, if_pos h2]

lemma scid3_Fc_hi (a b q : ℝ) (hab : a < b) (h : b ≤ q) : scid3_Fc a b q = 1 := by
  unfold scid3_Fc
  rw [if_neg (by linarith)]
  by_cases h2 : q ≤ b
  · rw [if_pos h2, show q = b by linarith, div_self (by linarith)]
  · rw [if_neg h2]

theorem scid3_prop2 (P : Params) (ha₁0 : 0 ≤ P.a₁) (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    (P.τbarIS p ≤ P.ξ → ∀ Q : ℝ, P.IsOptimalQuantity p Q ↔ Q = P.qHigh p) ∧
    (P.τlowIS p ≤ P.ξ → P.ξ ≤ P.τbarIS p → ∀ Q : ℝ, P.IsOptimalQuantity p Q ↔ Q = P.qMid p) ∧
    (P.ξ ≤ P.τlowIS p → ∀ Q : ℝ, P.IsOptimalQuantity p Q ↔ Q = P.qLow p) := by
  obtain ⟨hp0, hp1⟩ := hp
  have hL0 : 0 < P.b₀ - P.a₀ := by linarith
  have hL1 : 0 < P.b₁ - P.a₁ := by linarith
  have hd : 0 < P.a₀ - P.a₁ := by linarith
  refine ⟨fun hτ => ?_, fun hτl hτu => ?_, fun hτ => ?_⟩
  · -- high regime
    unfold Params.τbarIS at hτ
    have hτ' : (1 - P.ξ) * (P.b₀ - P.a₀) ≤ p * (P.b₀ - P.b₁) := by
      have : 1 - P.ξ ≤ p * (P.b₀ - P.b₁) / (P.b₀ - P.a₀) := by linarith
      rwa [le_div_iff₀ hL0] at this
    have hpp : 0 < p := by
      rcases eq_or_lt_of_le hp0 with h | h
      · subst h; nlinarith
      · exact h
    set t := (P.ξ - (1 - p)) * (P.b₀ - P.a₀) / p with ht_def
    have ht : t * p = (P.ξ - (1 - p)) * (P.b₀ - P.a₀) := div_mul_cancel₀ _ hpp.ne'
    have hq : P.qHigh p = t + P.a₀ := rfl
    have htlo : P.b₁ - P.a₀ ≤ t := by nlinarith
    have hthi : t < P.b₀ - P.a₀ := by nlinarith
    rw [hq]
    apply scid3_opt_iff P hb hm ha p ⟨hp0, hp1⟩ _ (by linarith)
    · rw [scid3_Fc_mid _ _ _ (by linarith) (by linarith) (by linarith),
        scid3_Fc_hi _ _ _ (by linarith) (by linarith)]
      field_simp
      linear_combination ht
    · right; exact ⟨hpp, by linarith, by linarith⟩
  · -- middle regime
    unfold Params.τbarIS at hτu
    unfold Params.τlowIS at hτl
    have hl : (1 - p) * (P.a₀ - P.a₁) ≤ P.ξ * (P.b₁ - P.a₁) := by
      rwa [div_le_iff₀ hL1] at hτl
    have hu : P.ξ * (P.b₀ - P.a₀) ≤ (P.b₀ - P.a₀) - p * (P.b₀ - P.b₁) := by
      have : p * (P.b₀ - P.b₁) / (P.b₀ - P.a₀) ≤ 1 - P.ξ := by linarith
      rw [div_le_iff₀ hL0] at this; linarith
    set N := (1 - p) * (P.b₀ - P.a₀) + p * (P.b₁ - P.a₁) with hN
    have hNp : 0 < N := by
      rcases eq_or_lt_of_le hp0 with h | h
      · rw [hN, ← h]; linarith
      · have : 0 ≤ (1 - p) * (P.b₀ - P.a₀) := mul_nonneg (by linarith) hL0.le
        have : 0 < p * (P.b₁ - P.a₁) := mul_pos h hL1
        linarith
    set t := (P.b₀ - P.a₀) * ((P.b₁ - P.a₁) * P.ξ - (1 - p) * (P.a₀ - P.a₁)) / N with ht_def
    have ht : t * N = (P.b₀ - P.a₀) * ((P.b₁ - P.a₁) * P.ξ - (1 - p) * (P.a₀ - P.a₁)) :=
      div_mul_cancel₀ _ hNp.ne'
    have hq : P.qMid p = t + P.a₀ := rfl
    have htlo : 0 ≤ t := by
      have : 0 ≤ t * N := by rw [ht]; apply mul_nonneg hL0.le; linarith
      exact nonneg_of_mul_nonneg_left this hNp
    have hthi : t ≤ P.b₁ - P.a₀ := by
      have key : t * N ≤ (P.b₁ - P.a₀) * N := by
        rw [ht, hN]
        have := mul_le_mul_of_nonneg_left hu hL1.le
        nlinarith
      exact le_of_mul_le_mul_right key hNp
    rw [hq]
    apply scid3_opt_iff P hb hm ha p ⟨hp0, hp1⟩ _ (by linarith)
    · rw [scid3_Fc_mid _ _ _ (by linarith) (by linarith) (by linarith),
        scid3_Fc_mid _ _ _ (by linarith) (by linarith) (by linarith)]
      field_simp
      linear_combination ht
    · by_cases c : p < 1 ∧ t + P.a₀ < P.b₁
      · left; exact ⟨by linarith [c.1], by linarith, c.2⟩
      · right
        rcases not_and_or.mp c with c1 | c2
        · have hp1' : p = 1 := le_antisymm hp1 (not_lt.mp c1)
          have : 0 < t := by
            have : 0 < t * N := by
              rw [ht, hp1']; apply mul_pos hL0; nlinarith
            exact pos_of_mul_pos_left this hNp.le
          exact ⟨by linarith, by linarith, by linarith⟩
        · have htb : t = P.b₁ - P.a₀ := le_antisymm hthi (by linarith [not_lt.mp c2])
          refine ⟨?_, by linarith, by linarith⟩
          rcases eq_or_lt_of_le hp0 with h | h
          · exfalso
            rw [← h] at ht hN
            rw [hN, htb] at ht
            have e : (P.b₀ - P.a₀) * ((P.b₁ - P.a₁) * (1 - P.ξ)) = 0 := by linarith [ht]
            rcases mul_eq_zero.mp e with e | e
            · linarith
            · rcases mul_eq_zero.mp e with e | e <;> linarith
          · exact h
  · -- low regime
    unfold Params.τlowIS at hτ
    have hl : P.ξ * (P.b₁ - P.a₁) ≤ (1 - p) * (P.a₀ - P.a₁) := by
      rwa [le_div_iff₀ hL1] at hτ
    have h1p : 0 < 1 - p := by
      by_contra h
      have : (1 - p) * (P.a₀ - P.a₁) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
      nlinarith [mul_pos hξ0 hL1]
    set t := P.ξ * (P.b₁ - P.a₁) / (1 - p) with ht_def
    have ht : t * (1 - p) = P.ξ * (P.b₁ - P.a₁) := div_mul_cancel₀ _ h1p.ne'
    have hq : P.qLow p = t + P.a₁ := rfl
    have htpos : 0 < t := by positivity
    have hthi : t ≤ P.a₀ - P.a₁ := by
      have : t * (1 - p) ≤ (P.a₀ - P.a₁) * (1 - p) := by rw [ht]; linarith
      exact le_of_mul_le_mul_right this h1p
    rw [hq]
    apply scid3_opt_iff P hb hm ha p ⟨hp0, hp1⟩ _ (by linarith)
    · rw [scid3_Fc_lo _ _ _ (by linarith),
        scid3_Fc_mid _ _ _ (by linarith) (by linarith) (by linarith)]
      field_simp
      linear_combination ht
    · left; exact ⟨h1p, by linarith, by linarith⟩
lemma scid3_K_nonneg (P : Params) (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) : 0 ≤ P.K p := by
  obtain ⟨hp0, hp1⟩ := hp
  have gnn : ∀ a b Q : ℝ, a < b → 0 ≤ scid3_gc a b Q := by
    intro a b Q hab
    unfold scid3_gc
    split_ifs with h1 h2
    · linarith
    · have : 0 < b - a := by linarith
      positivity
    · rfl
  unfold Params.K Params.retailerCost
  rw [scid3_mean_pos _ _ _ (by linarith), scid3_mean_pos _ _ _ (by linarith)]
  have := gnn P.a₀ P.b₀ (P.prefQ p) (by linarith)
  have := gnn P.a₁ P.b₁ (P.prefQ p) (by linarith)
  have : 0 ≤ 1 - p := by linarith
  positivity


lemma scid3_prefQ_eq (P : Params) (p q : ℝ) (h : ∀ Q, P.IsOptimalQuantity p Q ↔ Q = q) :
    P.prefQ p = q := by
  have hset : {Q | P.IsOptimalQuantity p Q} = {q} := Set.ext fun Q => h Q
  show sSup {Q | P.IsOptimalQuantity p Q} = q
  rw [hset, csSup_singleton]

lemma scid3_gc_lo (a b Q : ℝ) (h : Q ≤ a) : scid3_gc a b Q = (a + b) / 2 - Q := by
  unfold scid3_gc; rw [if_pos h]

lemma scid3_gc_mid (a b Q : ℝ) (hab : a < b) (h1 : a ≤ Q) (h2 : Q ≤ b) :
    scid3_gc a b Q = (b - Q) ^ 2 / (2 * (b - a)) := by
  unfold scid3_gc
  by_cases h : Q ≤ a
  · rw [if_pos h, show Q = a by linarith]
    field_simp [show b - a ≠ 0 by linarith]; ring
  · rw [if_neg h, if_pos h2]

lemma scid3_gc_hi (a b Q : ℝ) (hab : a < b) (h : b ≤ Q) : scid3_gc a b Q = 0 := by
  unfold scid3_gc
  rw [if_neg (by linarith)]
  by_cases h2 : Q ≤ b
  · rw [if_pos h2, show Q = b by linarith]; simp
  · rw [if_neg h2]

lemma scid3_K_eq (P : Params) (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (x : ℝ) : P.K x = x * scid3_gc P.a₀ P.b₀ (P.prefQ x) +
      (1 - x) * scid3_gc P.a₁ P.b₁ (P.prefQ x) := by
  unfold Params.K Params.retailerCost
  rw [scid3_mean_pos _ _ _ (by linarith), scid3_mean_pos _ _ _ (by linarith)]

/-- the closed forms of K in the three regimes, in the δ-notation -/
noncomputable def scid3_Low (P : Params) (x : ℝ) : ℝ :=
  (P.b₁ - P.a₁) / 2 + x * ((P.a₀ - P.a₁) + (P.b₀ - P.b₁)) / 2 -
    P.ξ * (2 - P.ξ) * (P.b₁ - P.a₁) / (2 * (1 - x))

noncomputable def scid3_Mid (P : Params) (x : ℝ) : ℝ :=
  ((1 - P.ξ) ^ 2 * (P.b₀ - P.a₀) * (P.b₁ - P.a₁) + (P.b₀ - P.b₁) ^ 2 * x * (1 - x)) /
    (2 * ((P.b₀ - P.a₀) + ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) * x))

noncomputable def scid3_High (P : Params) (x : ℝ) : ℝ :=
  (1 - P.ξ) ^ 2 * (P.b₀ - P.a₀) / (2 * x)

lemma scid3_K_low (P : Params) (ha₁0 : 0 ≤ P.a₁) (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) (hτ : P.ξ ≤ P.τlowIS x) :
    P.K x = scid3_Low P x := by
  have hq := scid3_prefQ_eq P x _ ((scid3_prop2 P ha₁0 hξ0 hξ1 hb hm ha x hx).2.2 hτ)
  obtain ⟨hx0, hx1⟩ := hx
  have hL1 : 0 < P.b₁ - P.a₁ := by linarith
  have hd : 0 < P.a₀ - P.a₁ := by linarith
  unfold Params.τlowIS at hτ
  have hl : P.ξ * (P.b₁ - P.a₁) ≤ (1 - x) * (P.a₀ - P.a₁) := by
    rwa [le_div_iff₀ hL1] at hτ
  have h1p : 0 < 1 - x := by
    by_contra h
    have : (1 - x) * (P.a₀ - P.a₁) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
    nlinarith [mul_pos hξ0 hL1]
  set t := P.ξ * (P.b₁ - P.a₁) / (1 - x) with ht_def
  have ht : t * (1 - x) = P.ξ * (P.b₁ - P.a₁) := div_mul_cancel₀ _ h1p.ne'
  have htpos : 0 < t := by positivity
  have hthi : t ≤ P.a₀ - P.a₁ := by
    have : t * (1 - x) ≤ (P.a₀ - P.a₁) * (1 - x) := by rw [ht]; linarith
    exact le_of_mul_le_mul_right this h1p
  rw [scid3_K_eq P hb hm ha, hq, show P.qLow x = t + P.a₁ from rfl,
    scid3_gc_lo _ _ _ (by linarith), scid3_gc_mid _ _ _ (by linarith) (by linarith) (by linarith)]
  unfold scid3_Low
  rw [ht_def]
  field_simp
  ring

lemma scid3_K_mid (P : Params) (ha₁0 : 0 ≤ P.a₁) (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) (hτl : P.τlowIS x ≤ P.ξ) (hτu : P.ξ ≤ P.τbarIS x) :
    P.K x = scid3_Mid P x := by
  have hq := scid3_prefQ_eq P x _ ((scid3_prop2 P ha₁0 hξ0 hξ1 hb hm ha x hx).2.1 hτl hτu)
  obtain ⟨hp0, hp1⟩ := hx
  have hL0 : 0 < P.b₀ - P.a₀ := by linarith
  have hL1 : 0 < P.b₁ - P.a₁ := by linarith
  unfold Params.τbarIS at hτu
  unfold Params.τlowIS at hτl
  have hl : (1 - x) * (P.a₀ - P.a₁) ≤ P.ξ * (P.b₁ - P.a₁) := by
    rwa [div_le_iff₀ hL1] at hτl
  have hu : P.ξ * (P.b₀ - P.a₀) ≤ (P.b₀ - P.a₀) - x * (P.b₀ - P.b₁) := by
    have : x * (P.b₀ - P.b₁) / (P.b₀ - P.a₀) ≤ 1 - P.ξ := by linarith
    rw [div_le_iff₀ hL0] at this; linarith
  set N := (1 - x) * (P.b₀ - P.a₀) + x * (P.b₁ - P.a₁) with hN
  have hNp : 0 < N := by
    rcases eq_or_lt_of_le hp0 with h | h
    · rw [hN, ← h]; linarith
    · have : 0 ≤ (1 - x) * (P.b₀ - P.a₀) := mul_nonneg (by linarith) hL0.le
      have : 0 < x * (P.b₁ - P.a₁) := mul_pos h hL1
      linarith
  set t := (P.b₀ - P.a₀) * ((P.b₁ - P.a₁) * P.ξ - (1 - x) * (P.a₀ - P.a₁)) / N with ht_def
  have ht : t * N = (P.b₀ - P.a₀) * ((P.b₁ - P.a₁) * P.ξ - (1 - x) * (P.a₀ - P.a₁)) :=
    div_mul_cancel₀ _ hNp.ne'
  have htlo : 0 ≤ t := by
    have : 0 ≤ t * N := by rw [ht]; apply mul_nonneg hL0.le; linarith
    exact nonneg_of_mul_nonneg_left this hNp
  have hthi : t ≤ P.b₁ - P.a₀ := by
    have key : t * N ≤ (P.b₁ - P.a₀) * N := by
      rw [ht, hN]
      have := mul_le_mul_of_nonneg_left hu hL1.le
      nlinarith
    exact le_of_mul_le_mul_right key hNp
  rw [scid3_K_eq P hb hm ha, hq, show P.qMid x = t + P.a₀ from rfl,
    scid3_gc_mid _ _ _ (by linarith) (by linarith) (by linarith),
    scid3_gc_mid _ _ _ (by linarith) (by linarith) (by linarith)]
  unfold scid3_Mid
  have hN' : (P.b₀ - P.a₀) + ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) * x = N := by rw [hN]; ring
  rw [hN', ht_def]
  field_simp
  ring

lemma scid3_K_high (P : Params) (ha₁0 : 0 ≤ P.a₁) (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) (hτ : P.τbarIS x ≤ P.ξ) :
    P.K x = scid3_High P x := by
  have hq := scid3_prefQ_eq P x _ ((scid3_prop2 P ha₁0 hξ0 hξ1 hb hm ha x hx).1 hτ)
  obtain ⟨hp0, hp1⟩ := hx
  have hL0 : 0 < P.b₀ - P.a₀ := by linarith
  unfold Params.τbarIS at hτ
  have hτ' : (1 - P.ξ) * (P.b₀ - P.a₀) ≤ x * (P.b₀ - P.b₁) := by
    have : 1 - P.ξ ≤ x * (P.b₀ - P.b₁) / (P.b₀ - P.a₀) := by linarith
    rwa [le_div_iff₀ hL0] at this
  have hpp : 0 < x := by
    rcases eq_or_lt_of_le hp0 with h | h
    · subst h; nlinarith
    · exact h
  set t := (P.ξ - (1 - x)) * (P.b₀ - P.a₀) / x with ht_def
  have ht : t * x = (P.ξ - (1 - x)) * (P.b₀ - P.a₀) := div_mul_cancel₀ _ hpp.ne'
  have htlo : P.b₁ - P.a₀ ≤ t := by nlinarith
  have hthi : t < P.b₀ - P.a₀ := by nlinarith
  rw [scid3_K_eq P hb hm ha, hq, show P.qHigh x = t + P.a₀ from rfl,
    scid3_gc_mid _ _ _ (by linarith) (by linarith) (by linarith),
    scid3_gc_hi _ _ _ (by linarith) (by linarith)]
  unfold scid3_High
  rw [ht_def]
  field_simp
  ring

open BiconvexProg.BranchBound

lemma scid3_g_dec (a0 b0 a1 b1 ξ x : ℝ)
    (hN : (b0 - a0) + ((a0 - a1) - (b0 - b1)) * x ≠ 0) (hdu : (a0 - a1) - (b0 - b1) ≠ 0) :
    ((1 - ξ) ^ 2 * (b0 - a0) * (b1 - a1) + (b0 - b1) ^ 2 * x * (1 - x)) /
      (2 * ((b0 - a0) + ((a0 - a1) - (b0 - b1)) * x)) =
    (b0 - b1) ^ 2 * (b1 - a1) / (2 * ((a0 - a1) - (b0 - b1)) ^ 2) +
      (-(b0 - b1) ^ 2 / (2 * ((a0 - a1) - (b0 - b1)))) * x +
      ((b0 - a0) * (b1 - a1) * ((a0 - a1) * (1 - ξ) + (b0 - b1) * ξ) *
        (((a0 - a1) - 2 * (b0 - b1)) - ξ * ((a0 - a1) - (b0 - b1))) /
        (2 * ((a0 - a1) - (b0 - b1)) ^ 2)) *
      (1 / ((b0 - a0) + ((a0 - a1) - (b0 - b1)) * x)) := by
  have hx : x = ((b0 - a0) + ((a0 - a1) - (b0 - b1)) * x - (b0 - a0)) / ((a0 - a1) - (b0 - b1)) := by
    field_simp; ring
  generalize hn : (b0 - a0) + ((a0 - a1) - (b0 - b1)) * x = n at hN hx ⊢
  rw [hx]
  field_simp
  ring

lemma scid3_g_midch (a0 b0 a1 b1 ξ x : ℝ)
    (hN : (b0 - a0) + ((a0 - a1) - (b0 - b1)) * x ≠ 0) :
    ((1 - ξ) ^ 2 * (b0 - a0) * (b1 - a1) + (b0 - b1) ^ 2 * x * (1 - x)) /
      (2 * ((b0 - a0) + ((a0 - a1) - (b0 - b1)) * x)) -
    ((1 - ξ) ^ 2 * (b1 - a1) / 2 + ((1 - ξ) ^ 2 * (b0 - a0) / 2 - (1 - ξ) ^ 2 * (b1 - a1) / 2) * x) =
    x * (1 - x) * ((b0 - b1) - (1 - ξ) * ((a0 - a1) - (b0 - b1))) *
      ((b0 - b1) + (1 - ξ) * ((a0 - a1) - (b0 - b1))) /
      (2 * ((b0 - a0) + ((a0 - a1) - (b0 - b1)) * x)) := by
  rw [div_sub' (by positivity), div_left_inj' (by positivity)]
  ring

lemma scid3_g_highch (a0 b0 a1 b1 ξ x : ℝ) (hx : x ≠ 0) :
    (1 - ξ) ^ 2 * (b0 - a0) / (2 * x) -
    ((1 - ξ) ^ 2 * (b1 - a1) / 2 + ((1 - ξ) ^ 2 * (b0 - a0) / 2 - (1 - ξ) ^ 2 * (b1 - a1) / 2) * x) =
    (1 - ξ) ^ 2 * (1 - x) * ((b0 - a0) + x * ((b0 - b1) - (a0 - a1))) / (2 * x) := by
  field_simp; ring

lemma scid3_g_lowch (a0 b0 a1 b1 ξ x : ℝ) (h1x : 1 - x ≠ 0) :
    ((b1 - a1) / 2 + x * ((a0 - a1) + (b0 - b1)) / 2 - ξ * (2 - ξ) * (b1 - a1) / (2 * (1 - x))) -
    ((1 - ξ) ^ 2 * (b1 - a1) / 2 + ((1 - ξ) ^ 2 * (b0 - a0) / 2 - (1 - ξ) ^ 2 * (b1 - a1) / 2) * x) =
    x / 2 * (((a0 - a1) + (b0 - b1)) + (1 - ξ) ^ 2 * ((a0 - a1) - (b0 - b1)) -
      (2 - ξ) * (ξ * (b1 - a1) / (1 - x))) := by
  field_simp; ring

lemma scid3_g_lowmid (a0 b0 a1 b1 ξ x : ℝ) (h1x : 1 - x ≠ 0)
    (hN : (b0 - a0) + ((a0 - a1) - (b0 - b1)) * x ≠ 0) :
    ((b1 - a1) / 2 + x * ((a0 - a1) + (b0 - b1)) / 2 - ξ * (2 - ξ) * (b1 - a1) / (2 * (1 - x))) -
    ((1 - ξ) ^ 2 * (b0 - a0) * (b1 - a1) + (b0 - b1) ^ 2 * x * (1 - x)) /
      (2 * ((b0 - a0) + ((a0 - a1) - (b0 - b1)) * x)) =
    x * ((a0 - a1) - (a0 - a1) * x - ξ * (b1 - a1)) *
      ((a0 - a1) * x + (a0 - a1) * (1 - ξ) + (b1 - a0) * (2 - ξ)) /
      (2 * (1 - x) * ((b0 - a0) + ((a0 - a1) - (b0 - b1)) * x)) := by
  generalize hn : (b0 - a0) + ((a0 - a1) - (b0 - b1)) * x = n at hN ⊢
  field_simp
  subst hn
  ring

lemma scid3_g_lowl (a0 b0 a1 b1 ξ x : ℝ) (h1x : 1 - x ≠ 0)
    (hpb : 1 - ξ * (b1 - a1) / (a0 - a1) ≠ 0) (h1pb : 1 - (1 - ξ * (b1 - a1) / (a0 - a1)) ≠ 0)
    (hd : a0 - a1 ≠ 0) :
    ((b1 - a1) / 2 + x * ((a0 - a1) + (b0 - b1)) / 2 - ξ * (2 - ξ) * (b1 - a1) / (2 * (1 - x))) -
    (((b1 - a1) / 2 + 0 * ((a0 - a1) + (b0 - b1)) / 2 - ξ * (2 - ξ) * (b1 - a1) / (2 * (1 - 0))) +
      ((((b1 - a1) / 2 + (1 - ξ * (b1 - a1) / (a0 - a1)) * ((a0 - a1) + (b0 - b1)) / 2 -
          ξ * (2 - ξ) * (b1 - a1) / (2 * (1 - (1 - ξ * (b1 - a1) / (a0 - a1))))) -
        ((b1 - a1) / 2 + 0 * ((a0 - a1) + (b0 - b1)) / 2 - ξ * (2 - ξ) * (b1 - a1) / (2 * (1 - 0))))
        / (1 - ξ * (b1 - a1) / (a0 - a1))) * x) =
    x * (2 - ξ) * ((a0 - a1) - (a0 - a1) * x - ξ * (b1 - a1)) / (2 * (1 - x)) := by
  generalize hq : ξ * (b1 - a1) / (a0 - a1) = q at hpb h1pb ⊢
  have hq' : ξ * (b1 - a1) = q * (a0 - a1) := by rw [← hq]; field_simp
  field_simp
  linear_combination (-x*(q-1)*(x-1)*(ξ-2)) * hq'

lemma scid3_g_midl (a0 b0 a1 b1 ξ x : ℝ)
    (hN : (b0 - a0) + ((a0 - a1) - (b0 - b1)) * x ≠ 0)
    (hpb : 1 - ξ * (b1 - a1) / (a0 - a1) ≠ 0) (h1pb : 1 - (1 - ξ * (b1 - a1) / (a0 - a1)) ≠ 0)
    (hd : a0 - a1 ≠ 0) :
    ((1 - ξ) ^ 2 * (b0 - a0) * (b1 - a1) + (b0 - b1) ^ 2 * x * (1 - x)) /
      (2 * ((b0 - a0) + ((a0 - a1) - (b0 - b1)) * x)) -
    (((b1 - a1) / 2 + 0 * ((a0 - a1) + (b0 - b1)) / 2 - ξ * (2 - ξ) * (b1 - a1) / (2 * (1 - 0))) +
      ((((b1 - a1) / 2 + (1 - ξ * (b1 - a1) / (a0 - a1)) * ((a0 - a1) + (b0 - b1)) / 2 -
          ξ * (2 - ξ) * (b1 - a1) / (2 * (1 - (1 - ξ * (b1 - a1) / (a0 - a1))))) -
        ((b1 - a1) / 2 + 0 * ((a0 - a1) + (b0 - b1)) / 2 - ξ * (2 - ξ) * (b1 - a1) / (2 * (1 - 0))))
        / (1 - ξ * (b1 - a1) / (a0 - a1))) * x) =
    x * ((a0 - a1) * x - (a0 - a1) + ξ * (b1 - a1)) *
      (((a0 - a1) - 2 * (b0 - b1)) - ξ * ((a0 - a1) - (b0 - b1))) /
      (2 * ((b0 - a0) + ((a0 - a1) - (b0 - b1)) * x)) := by
  generalize hq : ξ * (b1 - a1) / (a0 - a1) = q at hpb h1pb ⊢
  have hq' : ξ * (b1 - a1) = q * (a0 - a1) := by rw [← hq]; field_simp
  generalize hn : (b0 - a0) + ((a0 - a1) - (b0 - b1)) * x = n at hN ⊢
  field_simp
  subst hn
  linear_combination (x*(q - 1)*(ξ - 2)*(a0*x - a0 - a1*x - b0*x + b0 + b1*x)) * hq'


lemma scid3_env_eq (P : Params) (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (v : ℝ)
    (hup : ∀ g : ℝ → ℝ, ConvexOn ℝ (Set.Icc (0:ℝ) 1) g →
      (∀ w ∈ Set.Icc (0:ℝ) 1, g w ≤ P.K w) → g p ≤ v)
    (hlow : ∃ g : ℝ → ℝ, ConvexOn ℝ (Set.Icc (0:ℝ) 1) g ∧
      (∀ w ∈ Set.Icc (0:ℝ) 1, g w ≤ P.K w) ∧ g p = v) :
    convexEnvelope (Set.Icc (0:ℝ) 1) P.K p = v := by
  unfold convexEnvelope
  apply le_antisymm
  · apply csSup_le
    · exact ⟨0, fun _ => 0, convexOn_const 0 (convex_Icc 0 1),
        fun w hw => scid3_K_nonneg P hb hm ha w hw, rfl⟩
    · rintro r ⟨g, hg, hgK, rfl⟩
      exact hup g hg hgK
  · obtain ⟨g, hg, hgK, hgv⟩ := hlow
    apply le_csSup
    · refine ⟨P.K p, ?_⟩
      rintro r ⟨g', -, hg', rfl⟩
      exact hg' p hp
    · exact ⟨g, hg, hgK, hgv.symm⟩

lemma scid3_affine_convex (α β : ℝ) : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun x => α + β * x) := by
  refine ⟨convex_Icc 0 1, fun x _ y _ a b _ _ hab => le_of_eq ?_⟩
  simp only [smul_eq_mul]
  linear_combination (-α) * hab

lemma scid3_inv_comb (Y Z a b : ℝ) (hY : 0 < Y) (hZ : 0 < Z) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : 1 / (a * Y + b * Z) ≤ a / Y + b / Z := by
  have hpos : 0 < a * Y + b * Z := by
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h] at hab ⊢; rw [show b = 1 by linarith]; linarith
    · have := mul_pos h hY; have := mul_nonneg hb hZ.le; linarith
  rw [div_add_div _ _ hY.ne' hZ.ne', div_le_div_iff₀ hpos (by positivity)]
  have : 0 ≤ a * b * (Y - Z) ^ 2 := by have := mul_nonneg ha hb; positivity
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith

lemma scid3_Mid_convex (P : Params) (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (hdu : P.b₀ - P.b₁ < P.a₀ - P.a₁)
    (hξ : P.ξ * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) ≤ (P.a₀ - P.a₁) - 2 * (P.b₀ - P.b₁))
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1) :
    ConvexOn ℝ (Set.Icc (0:ℝ) 1) (scid3_Mid P) := by
  have hdu' : 0 < (P.a₀ - P.a₁) - (P.b₀ - P.b₁) := by linarith
  have hL0 : 0 < P.b₀ - P.a₀ := by linarith
  have hL1 : 0 < P.b₁ - P.a₁ := by linarith
  obtain ⟨A0, A1, C, hCnn, hdec⟩ : ∃ A0 A1 C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc (0:ℝ) 1,
      scid3_Mid P x = A0 + A1 * x +
        C * (1 / ((P.b₀ - P.a₀) + ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) * x)) := by
    refine ⟨(P.b₀ - P.b₁) ^ 2 * (P.b₁ - P.a₁) / (2 * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) ^ 2),
      -(P.b₀ - P.b₁) ^ 2 / (2 * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁))),
      (P.b₀ - P.a₀) * (P.b₁ - P.a₁) * ((P.a₀ - P.a₁) * (1 - P.ξ) + (P.b₀ - P.b₁) * P.ξ) *
        (((P.a₀ - P.a₁) - 2 * (P.b₀ - P.b₁)) - P.ξ * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁))) /
        (2 * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) ^ 2), ?_, fun x hx => ?_⟩
    · apply div_nonneg _ (by positivity)
      apply mul_nonneg (mul_nonneg (mul_nonneg hL0.le hL1.le) _) (by linarith)
      have : 0 ≤ (P.a₀ - P.a₁) * (1 - P.ξ) := mul_nonneg (by linarith) (by linarith)
      have : 0 ≤ (P.b₀ - P.b₁) * P.ξ := mul_nonneg (by linarith) hξ0.le
      linarith
    · have : 0 < (P.b₀ - P.a₀) + ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) * x := by
        have := mul_nonneg hdu'.le hx.1; linarith
      exact scid3_g_dec P.a₀ P.b₀ P.a₁ P.b₁ P.ξ x this.ne' hdu'.ne'
  have hNpos : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < (P.b₀ - P.a₀) + ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) * x := by
    intro x hx; have := mul_nonneg hdu'.le hx.1; linarith
  refine ⟨convex_Icc 0 1, fun y hy z hz a b ha0 hb0 hab => ?_⟩
  have hyz : a • y + b • z ∈ Set.Icc (0:ℝ) 1 := (convex_Icc 0 1) hy hz ha0 hb0 hab
  simp only [smul_eq_mul] at hyz ⊢
  rw [hdec _ hyz, hdec _ hy, hdec _ hz]
  set D := (P.a₀ - P.a₁) - (P.b₀ - P.b₁)
  have hcomb : (P.b₀ - P.a₀) + D * (a * y + b * z) =
      a * ((P.b₀ - P.a₀) + D * y) + b * ((P.b₀ - P.a₀) + D * z) := by
    have : (P.b₀ - P.a₀) = (a + b) * (P.b₀ - P.a₀) := by rw [hab]; ring
    linear_combination this
  rw [hcomb]
  have key := scid3_inv_comb _ _ a b (hNpos y hy) (hNpos z hz) ha0 hb0 hab
  have key' := mul_le_mul_of_nonneg_left key hCnn
  have e1 : a * (A0 + A1 * y + C * (1 / ((P.b₀ - P.a₀) + D * y))) +
      b * (A0 + A1 * z + C * (1 / ((P.b₀ - P.a₀) + D * z))) =
      (a + b) * A0 + A1 * (a * y + b * z) +
        C * (a / ((P.b₀ - P.a₀) + D * y) + b / ((P.b₀ - P.a₀) + D * z)) := by
    ring
  rw [e1, hab]
  linarith

set_option maxHeartbeats 1600000 in
theorem solution (P : Params) (ha₁0 : 0 ≤ P.a₁) (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (h2 : 2 * P.δu < P.δd) (hmax : max (P.δd - 2 * P.δu) (P.δd * P.δu / (P.δd - 2 * P.δu)) < P.δIS)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    (P.ξbreve ≤ P.ξ →
      convexEnvelope (Set.Icc (0:ℝ) 1) P.K p = (1 - p) * P.K 0 + p * P.K 1) ∧
    (P.τlowIS 0 ≤ P.ξ → P.ξ < P.ξbreve →
      convexEnvelope (Set.Icc (0:ℝ) 1) P.K p = P.K p) ∧
    (P.ξ < P.τlowIS 0 →
      convexEnvelope (Set.Icc (0:ℝ) 1) P.K p =
        if P.pbreve ≤ p then P.K p
        else p * (P.K P.pbreve - P.K 0) / P.pbreve + P.K 0) := by
  obtain ⟨hp0, hp1⟩ := hp
  -- notation
  have hδd : P.δd = P.a₀ - P.a₁ := rfl
  have hδu : P.δu = P.b₀ - P.b₁ := rfl
  have hδIS : P.δIS = P.b₁ - P.a₀ := rfl
  have hu : 0 < P.b₀ - P.b₁ := by linarith
  have hd : 0 < P.a₀ - P.a₁ := by linarith
  have hs : 0 < P.b₁ - P.a₀ := by linarith
  have hL0 : 0 < P.b₀ - P.a₀ := by linarith
  have hL1 : 0 < P.b₁ - P.a₁ := by linarith
  have h2' : 2 * (P.b₀ - P.b₁) < P.a₀ - P.a₁ := by rw [← hδd, ← hδu]; exact h2
  have hdu : 0 < (P.a₀ - P.a₁) - (P.b₀ - P.b₁) := by linarith
  have hd2u : 0 < (P.a₀ - P.a₁) - 2 * (P.b₀ - P.b₁) := by linarith
  have hs1 : (P.a₀ - P.a₁) - 2 * (P.b₀ - P.b₁) < P.b₁ - P.a₀ := by
    have := lt_of_le_of_lt (le_max_left _ _) hmax
    rw [hδd, hδu, hδIS] at this; exact this
  have hs2 : (P.a₀ - P.a₁) * (P.b₀ - P.b₁) < (P.b₁ - P.a₀) * ((P.a₀ - P.a₁) - 2 * (P.b₀ - P.b₁)) := by
    have := lt_of_le_of_lt (le_max_right _ _) hmax
    rw [hδd, hδu, hδIS, div_lt_iff₀ (by linarith)] at this; exact this
  have hxb : P.ξbreve = ((P.a₀ - P.a₁) - 2 * (P.b₀ - P.b₁)) / ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) := by
    unfold Params.ξbreve; rw [hδd, hδu]
  -- ξ vs ξ̆ in product form
  have hbreve_iff : P.ξbreve ≤ P.ξ ↔
      (P.a₀ - P.a₁) - 2 * (P.b₀ - P.b₁) ≤ P.ξ * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) := by
    rw [hxb, div_le_iff₀ hdu]
  have hpos01 : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < (P.b₀ - P.a₀) + ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) * x :=
    fun x hx => by have := mul_nonneg hdu.le hx.1; linarith
  -- regime facts
  have hlow_iff : ∀ x, P.ξ ≤ P.τlowIS x ↔ P.ξ * (P.b₁ - P.a₁) ≤ (1 - x) * (P.a₀ - P.a₁) := by
    intro x; unfold Params.τlowIS; rw [le_div_iff₀ hL1]
  have hbar_iff : ∀ x, P.τbarIS x ≤ P.ξ ↔ (1 - P.ξ) * (P.b₀ - P.a₀) ≤ x * (P.b₀ - P.b₁) := by
    intro x; unfold Params.τbarIS
    constructor
    · intro h
      have : 1 - P.ξ ≤ x * (P.b₀ - P.b₁) / (P.b₀ - P.a₀) := by linarith
      rwa [le_div_iff₀ hL0] at this
    · intro h
      have : 1 - P.ξ ≤ x * (P.b₀ - P.b₁) / (P.b₀ - P.a₀) := by rwa [le_div_iff₀ hL0]
      linarith
  -- K at the endpoints
  have hK0 : P.K 0 = (1 - P.ξ) ^ 2 * (P.b₁ - P.a₁) / 2 := by
    by_cases c : P.ξ ≤ P.τlowIS 0
    · rw [scid3_K_low P ha₁0 hξ0 hξ1 hb hm ha 0 ⟨le_refl 0, zero_le_one⟩ c]
      unfold scid3_Low; field_simp; ring
    · have hbar : P.ξ ≤ P.τbarIS 0 := by unfold Params.τbarIS; simp; linarith
      rw [scid3_K_mid P ha₁0 hξ0 hξ1 hb hm ha 0 ⟨le_refl 0, zero_le_one⟩
        (le_of_lt (not_le.mp c)) hbar]
      unfold scid3_Mid; field_simp; ring
  have hK1 : P.K 1 = (1 - P.ξ) ^ 2 * (P.b₀ - P.a₀) / 2 := by
    have hl : P.τlowIS 1 ≤ P.ξ := by unfold Params.τlowIS; simp; linarith
    by_cases c : P.τbarIS 1 ≤ P.ξ
    · rw [scid3_K_high P ha₁0 hξ0 hξ1 hb hm ha 1 ⟨zero_le_one, le_refl 1⟩ c]
      unfold scid3_High; field_simp
    · rw [scid3_K_mid P ha₁0 hξ0 hξ1 hb hm ha 1 ⟨zero_le_one, le_refl 1⟩ hl
        (le_of_lt (not_le.mp c))]
      unfold scid3_Mid
      have : (P.b₀ - P.a₀) + ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) * 1 = P.b₁ - P.a₁ := by ring
      rw [this]; field_simp; ring
  -- when ξ < ξ̆ there is no high regime
  have hnohigh : P.ξ < P.ξbreve → ∀ x ∈ Set.Icc (0:ℝ) 1, P.ξ ≤ P.τbarIS x := by
    intro hξb x hx
    have h1 : P.ξ * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) < (P.a₀ - P.a₁) - 2 * (P.b₀ - P.b₁) := by
      rw [hxb, lt_div_iff₀ hdu] at hξb; exact hξb
    by_contra hc
    have hc' := (hbar_iff x).1 (le_of_lt (not_le.mp hc))
    have : (1 - P.ξ) * (P.b₀ - P.a₀) ≤ P.b₀ - P.b₁ := by
      have := mul_le_mul_of_nonneg_right hx.2 hu.le; linarith
    -- (1-ξ)(s+u) ≤ u and ξ(d-u) < d-2u contradict s > d - 2u
    nlinarith
  refine ⟨fun hξ => ?_, fun hξl hξu => ?_, fun hξ => ?_⟩
  · ------------------------------------------------------------------ case 1
    have hξ' := hbreve_iff.1 hξ
    apply scid3_env_eq P hb hm ha p ⟨hp0, hp1⟩
    · intro g hg hgK
      have := hg.2 (show (0:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨le_refl 0, zero_le_one⟩)
        (show (1:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨zero_le_one, le_refl 1⟩)
        (show 0 ≤ 1 - p by linarith) hp0 (by ring)
      simp only [smul_eq_mul, mul_zero, mul_one, zero_add] at this
      have h0 := hgK 0 ⟨le_refl 0, zero_le_one⟩
      have h1 := hgK 1 ⟨zero_le_one, le_refl 1⟩
      have := mul_le_mul_of_nonneg_left h0 (show 0 ≤ 1 - p by linarith)
      have := mul_le_mul_of_nonneg_left h1 hp0
      linarith
    · refine ⟨fun x => P.K 0 + (P.K 1 - P.K 0) * x, scid3_affine_convex _ _, ?_, by ring⟩
      intro x hx
      obtain ⟨hx0, hx1⟩ := hx
      rw [hK0, hK1]
      by_cases c1 : P.ξ ≤ P.τlowIS x
      · rw [scid3_K_low P ha₁0 hξ0 hξ1 hb hm ha x ⟨hx0, hx1⟩ c1]
        have hl := (hlow_iff x).1 c1
        have h1x : 0 < 1 - x := by
          by_contra h
          have : (1 - x) * (P.a₀ - P.a₁) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
          nlinarith [mul_pos hξ0 hL1]
        set r := P.ξ * (P.b₁ - P.a₁) / (1 - x) with hr
        have hr1 : r * (1 - x) = P.ξ * (P.b₁ - P.a₁) := div_mul_cancel₀ _ h1x.ne'
        have hrd : r ≤ P.a₀ - P.a₁ := by
          have : r * (1 - x) ≤ (P.a₀ - P.a₁) * (1 - x) := by rw [hr1]; linarith
          exact le_of_mul_le_mul_right this h1x
        have key : scid3_Low P x - ((1 - P.ξ) ^ 2 * (P.b₁ - P.a₁) / 2 +
            ((1 - P.ξ) ^ 2 * (P.b₀ - P.a₀) / 2 - (1 - P.ξ) ^ 2 * (P.b₁ - P.a₁) / 2) * x) =
            x / 2 * (((P.a₀ - P.a₁) + (P.b₀ - P.b₁)) +
              (1 - P.ξ) ^ 2 * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) - (2 - P.ξ) * r) := by
          exact scid3_g_lowch P.a₀ P.b₀ P.a₁ P.b₁ P.ξ x h1x.ne'
        have hbr : 0 ≤ ((P.a₀ - P.a₁) + (P.b₀ - P.b₁)) +
            (1 - P.ξ) ^ 2 * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) - (2 - P.ξ) * r := by
          have e : ((P.a₀ - P.a₁) + (P.b₀ - P.b₁)) +
              (1 - P.ξ) ^ 2 * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) - (2 - P.ξ) * r =
              P.ξ * (P.ξ * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) - ((P.a₀ - P.a₁) - 2 * (P.b₀ - P.b₁)))
              + (2 - P.ξ) * ((P.a₀ - P.a₁) - r) := by ring
          rw [e]
          have := mul_nonneg hξ0.le (show 0 ≤ P.ξ * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) -
            ((P.a₀ - P.a₁) - 2 * (P.b₀ - P.b₁)) by linarith)
          have := mul_nonneg (show (0:ℝ) ≤ 2 - P.ξ by linarith)
            (show 0 ≤ (P.a₀ - P.a₁) - r by linarith)
          linarith
        have := mul_nonneg (div_nonneg hx0 (by norm_num : (0:ℝ) ≤ 2)) hbr
        linarith
      by_cases c2 : P.τbarIS x ≤ P.ξ
      · rw [scid3_K_high P ha₁0 hξ0 hξ1 hb hm ha x ⟨hx0, hx1⟩ c2]
        have hxpos : 0 < x := by
          rcases eq_or_lt_of_le hx0 with h | h
          · have := (hbar_iff x).1 c2; rw [← h] at this; nlinarith
          · exact h
        have key : scid3_High P x - ((1 - P.ξ) ^ 2 * (P.b₁ - P.a₁) / 2 +
            ((1 - P.ξ) ^ 2 * (P.b₀ - P.a₀) / 2 - (1 - P.ξ) ^ 2 * (P.b₁ - P.a₁) / 2) * x) =
            (1 - P.ξ) ^ 2 * (1 - x) * ((P.b₀ - P.a₀) + x * ((P.b₀ - P.b₁) - (P.a₀ - P.a₁))) /
              (2 * x) := by
          exact scid3_g_highch P.a₀ P.b₀ P.a₁ P.b₁ P.ξ x hxpos.ne'
        have hpos : 0 ≤ (P.b₀ - P.a₀) + x * ((P.b₀ - P.b₁) - (P.a₀ - P.a₁)) := by
          have : x * ((P.b₀ - P.b₁) - (P.a₀ - P.a₁)) ≥ 1 * ((P.b₀ - P.b₁) - (P.a₀ - P.a₁)) := by
            nlinarith
          linarith
        have : 0 ≤ (1 - P.ξ) ^ 2 * (1 - x) * ((P.b₀ - P.a₀) + x * ((P.b₀ - P.b₁) - (P.a₀ - P.a₁))) /
              (2 * x) := by
          apply div_nonneg _ (by positivity)
          apply mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) hpos
        linarith
      · rw [scid3_K_mid P ha₁0 hξ0 hξ1 hb hm ha x ⟨hx0, hx1⟩ (le_of_lt (not_le.mp c1))
          (le_of_lt (not_le.mp c2))]
        have hN := hpos01 x ⟨hx0, hx1⟩
        have key : scid3_Mid P x - ((1 - P.ξ) ^ 2 * (P.b₁ - P.a₁) / 2 +
            ((1 - P.ξ) ^ 2 * (P.b₀ - P.a₀) / 2 - (1 - P.ξ) ^ 2 * (P.b₁ - P.a₁) / 2) * x) =
            x * (1 - x) * ((P.b₀ - P.b₁) - (1 - P.ξ) * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁))) *
              ((P.b₀ - P.b₁) + (1 - P.ξ) * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁))) /
              (2 * ((P.b₀ - P.a₀) + ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) * x)) := by
          exact scid3_g_midch P.a₀ P.b₀ P.a₁ P.b₁ P.ξ x hN.ne'
        have : 0 ≤ x * (1 - x) * ((P.b₀ - P.b₁) - (1 - P.ξ) * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁))) *
              ((P.b₀ - P.b₁) + (1 - P.ξ) * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁))) /
              (2 * ((P.b₀ - P.a₀) + ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) * x)) := by
          apply div_nonneg _ (by positivity)
          apply mul_nonneg (mul_nonneg (mul_nonneg hx0 (by linarith)) (by linarith))
          have := mul_nonneg (show 0 ≤ 1 - P.ξ by linarith) hdu.le
          linarith
        linarith
  · ------------------------------------------------------------------ case 2
    have hξ'' : P.ξ * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) < (P.a₀ - P.a₁) - 2 * (P.b₀ - P.b₁) := by
      have h := hξu
      rw [hxb, lt_div_iff₀ hdu] at h
      exact h
    have hmidall : ∀ x ∈ Set.Icc (0:ℝ) 1, P.K x = scid3_Mid P x := by
      intro x hx
      have hτ : P.τlowIS x ≤ P.ξ := by
        have h1 : P.τlowIS x ≤ P.τlowIS 0 := by
          unfold Params.τlowIS
          rw [div_le_div_iff_of_pos_right hL1]
          have := mul_le_mul_of_nonneg_right (show 1 - x ≤ 1 - 0 by linarith [hx.1]) hd.le
          exact this
        exact le_trans h1 hξl
      exact scid3_K_mid P ha₁0 hξ0 hξ1 hb hm ha x hx hτ (hnohigh hξu x hx)
    have hconv : ConvexOn ℝ (Set.Icc (0:ℝ) 1) P.K :=
      (scid3_Mid_convex P hb hm ha (by linarith) hξ''.le hξ0 hξ1).congr
        (fun x hx => (hmidall x hx).symm)
    apply scid3_env_eq P hb hm ha p ⟨hp0, hp1⟩
    · intro g _ hgK; exact hgK p ⟨hp0, hp1⟩
    · exact ⟨P.K, hconv, fun _ _ => le_refl _, rfl⟩
  · ------------------------------------------------------------------ case 3
    have hτ0 : P.τlowIS 0 = (P.a₀ - P.a₁) / (P.b₁ - P.a₁) := by unfold Params.τlowIS; ring
    have hξd : P.ξ * (P.b₁ - P.a₁) < P.a₀ - P.a₁ := by
      rw [hτ0, lt_div_iff₀ hL1] at hξ; exact hξ
    have hξ'' : P.ξ * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) < (P.a₀ - P.a₁) - 2 * (P.b₀ - P.b₁) := by
      have e1 : P.ξ * (P.b₁ - P.a₁) * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) <
          (P.a₀ - P.a₁) * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) := mul_lt_mul_of_pos_right hξd hdu
      have e2 : (P.a₀ - P.a₁) * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) <
          ((P.a₀ - P.a₁) - 2 * (P.b₀ - P.b₁)) * (P.b₁ - P.a₁) := by
        have h := hs2
        have e : ((P.a₀ - P.a₁) - 2 * (P.b₀ - P.b₁)) * (P.b₁ - P.a₁) -
            (P.a₀ - P.a₁) * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) =
            (P.b₁ - P.a₀) * ((P.a₀ - P.a₁) - 2 * (P.b₀ - P.b₁)) -
            (P.a₀ - P.a₁) * (P.b₀ - P.b₁) := by ring
        linarith
      have e3 : P.ξ * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) * (P.b₁ - P.a₁) <
          ((P.a₀ - P.a₁) - 2 * (P.b₀ - P.b₁)) * (P.b₁ - P.a₁) := by
        have e : P.ξ * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) * (P.b₁ - P.a₁) =
          P.ξ * (P.b₁ - P.a₁) * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) := by ring
        linarith
      by_contra hc
      push_neg at hc
      have := mul_le_mul_of_nonneg_right hc hL1.le
      linarith
    have hξb : P.ξ < P.ξbreve := by
      rw [hxb]; exact (lt_div_iff₀ hdu).mpr hξ''
    have hξ' := hξ''.le
    have hpb_def : P.pbreve = 1 - P.ξ * (P.b₁ - P.a₁) / (P.a₀ - P.a₁) := rfl
    have hpb_pos : 0 < P.pbreve := by
      rw [hpb_def]
      have : P.ξ * (P.b₁ - P.a₁) / (P.a₀ - P.a₁) < 1 := by rw [div_lt_one hd]; exact hξd
      linarith
    have hpb_lt : P.pbreve < 1 := by
      rw [hpb_def]
      have : 0 < P.ξ * (P.b₁ - P.a₁) / (P.a₀ - P.a₁) := by positivity
      linarith
    have hpb_iff : ∀ x, P.pbreve ≤ x ↔ P.τlowIS x ≤ P.ξ := by
      intro x
      rw [hpb_def]
      unfold Params.τlowIS
      rw [div_le_iff₀ hL1]
      constructor
      · intro h
        have : 1 - x ≤ P.ξ * (P.b₁ - P.a₁) / (P.a₀ - P.a₁) := by linarith
        rw [le_div_iff₀ hd] at this; linarith
      · intro h
        have : 1 - x ≤ P.ξ * (P.b₁ - P.a₁) / (P.a₀ - P.a₁) := by rw [le_div_iff₀ hd]; linarith
        linarith
    have hMidle : ∀ x ∈ Set.Icc (0:ℝ) 1, scid3_Mid P x ≤ P.K x := by
      intro x hx
      by_cases c : P.ξ ≤ P.τlowIS x
      · rw [scid3_K_low P ha₁0 hξ0 hξ1 hb hm ha x hx c]
        have hl := (hlow_iff x).1 c
        have h1x : 0 < 1 - x := by
          by_contra h
          have : (1 - x) * (P.a₀ - P.a₁) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
          nlinarith [mul_pos hξ0 hL1]
        have hN := hpos01 x hx
        have key : scid3_Low P x - scid3_Mid P x =
            x * ((P.a₀ - P.a₁) - (P.a₀ - P.a₁) * x - P.ξ * (P.b₁ - P.a₁)) *
              ((P.a₀ - P.a₁) * x + (P.a₀ - P.a₁) * (1 - P.ξ) + (P.b₁ - P.a₀) * (2 - P.ξ)) /
              (2 * (1 - x) * ((P.b₀ - P.a₀) + ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) * x)) := by
          exact scid3_g_lowmid P.a₀ P.b₀ P.a₁ P.b₁ P.ξ x h1x.ne' hN.ne'
        have : 0 ≤ x * ((P.a₀ - P.a₁) - (P.a₀ - P.a₁) * x - P.ξ * (P.b₁ - P.a₁)) *
              ((P.a₀ - P.a₁) * x + (P.a₀ - P.a₁) * (1 - P.ξ) + (P.b₁ - P.a₀) * (2 - P.ξ)) /
              (2 * (1 - x) * ((P.b₀ - P.a₀) + ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) * x)) := by
          apply div_nonneg _ (by positivity)
          apply mul_nonneg (mul_nonneg hx.1 (by linarith))
          have := mul_nonneg hd.le hx.1
          have := mul_nonneg hd.le (show 0 ≤ 1 - P.ξ by linarith)
          have := mul_nonneg hs.le (show (0:ℝ) ≤ 2 - P.ξ by linarith)
          linarith
        linarith
      · rw [scid3_K_mid P ha₁0 hξ0 hξ1 hb hm ha x hx (le_of_lt (not_le.mp c))
          (hnohigh hξb x hx)]
    have hKpb : P.K P.pbreve = scid3_Low P P.pbreve := by
      apply scid3_K_low P ha₁0 hξ0 hξ1 hb hm ha _ ⟨hpb_pos.le, hpb_lt.le⟩
      rw [hlow_iff, hpb_def,
        show 1 - (1 - P.ξ * (P.b₁ - P.a₁) / (P.a₀ - P.a₁)) = P.ξ * (P.b₁ - P.a₁) / (P.a₀ - P.a₁)
          by ring, div_mul_cancel₀ _ hd.ne']
    have hK0' : P.K 0 = scid3_Low P 0 := by
      rw [hK0]; unfold scid3_Low; field_simp; ring
    apply scid3_env_eq P hb hm ha p ⟨hp0, hp1⟩
    · intro g hg hgK
      split_ifs with hc
      · exact hgK p ⟨hp0, hp1⟩
      · push_neg at hc
        set lam := p / P.pbreve with hlam
        have hlam0 : 0 ≤ lam := div_nonneg hp0 hpb_pos.le
        have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one hpb_pos]; exact hc.le
        have hconv := hg.2 (show (0:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨le_refl 0, zero_le_one⟩)
          (show P.pbreve ∈ Set.Icc (0:ℝ) 1 from ⟨hpb_pos.le, hpb_lt.le⟩)
          (show 0 ≤ 1 - lam by linarith) hlam0 (by ring)
        simp only [smul_eq_mul, mul_zero, zero_add] at hconv
        have hpe : lam * P.pbreve = p := by rw [hlam]; field_simp
        rw [hpe] at hconv
        have h0 := hgK 0 ⟨le_refl 0, zero_le_one⟩
        have h1 := hgK P.pbreve ⟨hpb_pos.le, hpb_lt.le⟩
        have := mul_le_mul_of_nonneg_left h0 (show 0 ≤ 1 - lam by linarith)
        have := mul_le_mul_of_nonneg_left h1 hlam0
        have e : p * (P.K P.pbreve - P.K 0) / P.pbreve + P.K 0 =
            (1 - lam) * P.K 0 + lam * P.K P.pbreve := by
          rw [hlam]; field_simp; ring
        rw [e]; linarith
    · split_ifs with hc
      · refine ⟨scid3_Mid P, scid3_Mid_convex P hb hm ha (by linarith) hξ' hξ0 hξ1, hMidle, ?_⟩
        exact (scid3_K_mid P ha₁0 hξ0 hξ1 hb hm ha p ⟨hp0, hp1⟩ ((hpb_iff p).1 hc)
          (hnohigh hξb p ⟨hp0, hp1⟩)).symm
      · refine ⟨fun x => P.K 0 + ((P.K P.pbreve - P.K 0) / P.pbreve) * x,
          scid3_affine_convex _ _, ?_, by simp only; ring⟩
        intro x hx
        simp only
        rw [hKpb, hK0']
        by_cases c : P.ξ ≤ P.τlowIS x
        · rw [scid3_K_low P ha₁0 hξ0 hξ1 hb hm ha x hx c]
          have hl := (hlow_iff x).1 c
          have h1x : 0 < 1 - x := by
            by_contra h
            have : (1 - x) * (P.a₀ - P.a₁) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
            nlinarith [mul_pos hξ0 hL1]
          have key : scid3_Low P x - (scid3_Low P 0 +
              ((scid3_Low P P.pbreve - scid3_Low P 0) / P.pbreve) * x) =
              x * (2 - P.ξ) * ((P.a₀ - P.a₁) - (P.a₀ - P.a₁) * x - P.ξ * (P.b₁ - P.a₁)) /
                (2 * (1 - x)) := by
            have h1pb : 1 - P.pbreve ≠ 0 := by linarith
            have hpbne : P.pbreve ≠ 0 := hpb_pos.ne'
            exact scid3_g_lowl P.a₀ P.b₀ P.a₁ P.b₁ P.ξ x h1x.ne' hpbne h1pb hd.ne'
          have : 0 ≤ x * (2 - P.ξ) * ((P.a₀ - P.a₁) - (P.a₀ - P.a₁) * x - P.ξ * (P.b₁ - P.a₁)) /
                (2 * (1 - x)) := by
            apply div_nonneg _ (by positivity)
            apply mul_nonneg (mul_nonneg hx.1 (by linarith)) (by linarith)
          linarith
        · rw [scid3_K_mid P ha₁0 hξ0 hξ1 hb hm ha x hx (le_of_lt (not_le.mp c))
            (hnohigh hξb x hx)]
          have hN := hpos01 x hx
          have hl : (1 - x) * (P.a₀ - P.a₁) ≤ P.ξ * (P.b₁ - P.a₁) := by
            have := not_le.mp c; rw [lt_iff_not_ge, hlow_iff] at this; push_neg at this
            exact this.le
          have key : scid3_Mid P x - (scid3_Low P 0 +
              ((scid3_Low P P.pbreve - scid3_Low P 0) / P.pbreve) * x) =
              x * ((P.a₀ - P.a₁) * x - (P.a₀ - P.a₁) + P.ξ * (P.b₁ - P.a₁)) *
                (((P.a₀ - P.a₁) - 2 * (P.b₀ - P.b₁)) - P.ξ * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁))) /
                (2 * ((P.b₀ - P.a₀) + ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) * x)) := by
            have h1pb : 1 - P.pbreve ≠ 0 := by linarith
            have hpbne : P.pbreve ≠ 0 := hpb_pos.ne'
            exact scid3_g_midl P.a₀ P.b₀ P.a₁ P.b₁ P.ξ x hN.ne' hpbne h1pb hd.ne'
          have : 0 ≤ x * ((P.a₀ - P.a₁) * x - (P.a₀ - P.a₁) + P.ξ * (P.b₁ - P.a₁)) *
                (((P.a₀ - P.a₁) - 2 * (P.b₀ - P.b₁)) - P.ξ * ((P.a₀ - P.a₁) - (P.b₀ - P.b₁))) /
                (2 * ((P.b₀ - P.a₀) + ((P.a₀ - P.a₁) - (P.b₀ - P.b₁)) * x)) := by
            apply div_nonneg _ (by positivity)
            apply mul_nonneg (mul_nonneg hx.1 (by linarith)) (by linarith)
          linarith
