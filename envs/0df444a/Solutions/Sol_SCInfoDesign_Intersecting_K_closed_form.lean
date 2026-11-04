-- Prove2me | solution 1 for SCInfoDesign.Intersecting.K_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T14:02:49.3031+00:00
-- url     : https://prove2.me/submissions/eea24e4e-a817-470a-874e-c15a19dbc883

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

lemma scid3_Kq_low (P : Params) (ha₁0 : 0 ≤ P.a₁) (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) (hτ : P.ξ ≤ P.τlowIS x) :
    P.K x = x * ((P.a₀ + P.b₀) / 2 - P.qLow x) +
        (1 - x) / (2 * (P.b₁ - P.a₁)) * (P.b₁ - P.qLow x) ^ 2 := by
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
  field_simp

lemma scid3_Kq_mid (P : Params) (ha₁0 : 0 ≤ P.a₁) (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) (hτl : P.τlowIS x ≤ P.ξ) (hτu : P.ξ ≤ P.τbarIS x) :
    P.K x = x / (2 * (P.b₀ - P.a₀)) * (P.b₀ - P.qMid x) ^ 2 +
        (1 - x) / (2 * (P.b₁ - P.a₁)) * (P.b₁ - P.qMid x) ^ 2 := by
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
  field_simp

lemma scid3_Kq_high (P : Params) (ha₁0 : 0 ≤ P.a₁) (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) (hτ : P.τbarIS x ≤ P.ξ) :
    P.K x = x / (2 * (P.b₀ - P.a₀)) * (P.b₀ - P.qHigh x) ^ 2 := by
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
  ring

theorem solution (P : Params) (ha₁0 : 0 ≤ P.a₁) (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    (P.τbarIS p ≤ P.ξ →
      P.K p = p / (2 * (P.b₀ - P.a₀)) * (P.b₀ - P.qHigh p) ^ 2) ∧
    (P.τlowIS p ≤ P.ξ → P.ξ ≤ P.τbarIS p →
      P.K p = p / (2 * (P.b₀ - P.a₀)) * (P.b₀ - P.qMid p) ^ 2 +
        (1 - p) / (2 * (P.b₁ - P.a₁)) * (P.b₁ - P.qMid p) ^ 2) ∧
    (P.ξ ≤ P.τlowIS p →
      P.K p = p * ((P.a₀ + P.b₀) / 2 - P.qLow p) +
        (1 - p) / (2 * (P.b₁ - P.a₁)) * (P.b₁ - P.qLow p) ^ 2) :=
  ⟨scid3_Kq_high P ha₁0 hξ0 hξ1 hb hm ha p hp,
   scid3_Kq_mid P ha₁0 hξ0 hξ1 hb hm ha p hp,
   scid3_Kq_low P ha₁0 hξ0 hξ1 hb hm ha p hp⟩
