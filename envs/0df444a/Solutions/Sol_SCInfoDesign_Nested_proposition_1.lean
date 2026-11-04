-- Prove2me | solution 1 for SCInfoDesign.Nested.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T19:06:34.061582+00:00
-- url     : https://prove2.me/submissions/41735275-a6c9-441e-bffb-6c25047dc9fd

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Nested_Setting

open SCInfoDesign.Nested

noncomputable def nsc_gc (a b Q : ℝ) : ℝ :=
  if Q ≤ a then (a + b) / 2 - Q else if Q ≤ b then (b - Q) ^ 2 / (2 * (b - a)) else 0

noncomputable def nsc_Fc (a b q : ℝ) : ℝ :=
  if q ≤ a then 0 else if q ≤ b then (q - a) / (b - a) else 1

lemma nsc_int_pos (a b Q : ℝ) (hab : a < b) :
    ∫ x in a..b, max (x - Q) 0 = (b - a) * nsc_gc a b Q := by
  have hba : (b - a) ≠ 0 := by linarith
  unfold nsc_gc
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

lemma nsc_mean_pos (a b Q : ℝ) (hab : a < b) :
    SCInfoDesign.Nested.uniformMean a b (fun d => max (d - Q) 0) = nsc_gc a b Q := by
  unfold SCInfoDesign.Nested.uniformMean
  rw [nsc_int_pos a b Q hab]
  field_simp [show b - a ≠ 0 by linarith]

lemma nsc_mean_supp (a b Q ξ : ℝ) (hab : a < b) :
    SCInfoDesign.Nested.uniformMean a b
      (fun d => ξ * max (d - Q) 0 + (1 - ξ) * max (Q - d) 0) =
      nsc_gc a b Q - (1 - ξ) * ((a + b) / 2 - Q) := by
  have hpt : (fun d => ξ * max (d - Q) 0 + (1 - ξ) * max (Q - d) 0) =
      fun d => max (d - Q) 0 - (1 - ξ) * (d - Q) := by
    funext d
    rcases le_total d Q with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have hc : Continuous fun x : ℝ => max (x - Q) 0 := by fun_prop
  unfold SCInfoDesign.Nested.uniformMean
  rw [hpt, intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
    (by apply Continuous.intervalIntegrable; fun_prop), nsc_int_pos a b Q hab,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    intervalIntegral.intervalIntegrable_id intervalIntegrable_const]
  simp [integral_id]
  field_simp [show b - a ≠ 0 by linarith]
  ring

lemma nsc_U (a b q Q : ℝ) (hab : a < b) :
    nsc_gc a b q - (1 - nsc_Fc a b q) * (Q - q) ≤ nsc_gc a b Q ∧
    (a < q → q < b → Q ≠ q →
      nsc_gc a b q - (1 - nsc_Fc a b q) * (Q - q) < nsc_gc a b Q) := by
  have hL : 0 < b - a := by linarith
  have hL' : b - a ≠ 0 := hL.ne'
  -- value of gc at Q
  have gQ : (Q ≤ a ∧ nsc_gc a b Q = (a + b) / 2 - Q) ∨
      (a < Q ∧ Q ≤ b ∧ nsc_gc a b Q = (b - Q) ^ 2 / (2 * (b - a))) ∨
      (b < Q ∧ nsc_gc a b Q = 0) := by
    unfold nsc_gc
    by_cases h1 : Q ≤ a
    · left; exact ⟨h1, by rw [if_pos h1]⟩
    · by_cases h2 : Q ≤ b
      · right; left; exact ⟨not_le.mp h1, h2, by rw [if_neg h1, if_pos h2]⟩
      · right; right; exact ⟨not_le.mp h2, by rw [if_neg h1, if_neg h2]⟩
  have gnn : 0 ≤ nsc_gc a b Q := by
    rcases gQ with ⟨h, e⟩ | ⟨h, h', e⟩ | ⟨h, e⟩ <;> rw [e]
    · linarith
    · positivity
  by_cases hq1 : q ≤ a
  · have e1 : nsc_gc a b q - (1 - nsc_Fc a b q) * (Q - q) = (a + b) / 2 - Q := by
      unfold nsc_gc nsc_Fc; rw [if_pos hq1, if_pos hq1]; ring
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
    have e1 : nsc_gc a b q - (1 - nsc_Fc a b q) * (Q - q) =
        (b - q) ^ 2 / (2 * (b - a)) - (b - q) / (b - a) * (Q - q) := by
      unfold nsc_gc nsc_Fc; rw [if_neg hq1, if_pos hq2, if_neg hq1, if_pos hq2]
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
  · have e1 : nsc_gc a b q - (1 - nsc_Fc a b q) * (Q - q) = 0 := by
      unfold nsc_gc nsc_Fc; rw [if_neg hq1, if_neg hq2, if_neg hq1, if_neg hq2]; ring
    rw [e1]
    exact ⟨gnn, fun _ h => absurd h (by linarith [not_le.mp hq2])⟩

lemma nsc_opt_iff (P : Params) (h0 : P.a₀ < P.b₀) (h1 : P.a₁ < P.b₁)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (q : ℝ) (hq0 : 0 ≤ q)
    (hF : p * nsc_Fc P.a₀ P.b₀ q + (1 - p) * nsc_Fc P.a₁ P.b₁ q = P.ξ)
    (hstrict : (0 < 1 - p ∧ P.a₁ < q ∧ q < P.b₁) ∨ (0 < p ∧ P.a₀ < q ∧ q < P.b₀)) :
    ∀ Q, P.IsOptimalQuantity p Q ↔ Q = q := by
  obtain ⟨hp0, hp1⟩ := hp
  have hS : ∀ Q, P.supplierCost p Q =
      p * (nsc_gc P.a₀ P.b₀ Q - (1 - P.ξ) * ((P.a₀ + P.b₀) / 2 - Q)) +
      (1 - p) * (nsc_gc P.a₁ P.b₁ Q - (1 - P.ξ) * ((P.a₁ + P.b₁) / 2 - Q)) := by
    intro Q
    unfold Params.supplierCost
    rw [nsc_mean_supp _ _ _ _ h0, nsc_mean_supp _ _ _ _ h1]
  have hdiff : ∀ Q, P.supplierCost p Q - P.supplierCost p q =
      p * (nsc_gc P.a₀ P.b₀ Q - (nsc_gc P.a₀ P.b₀ q - (1 - nsc_Fc P.a₀ P.b₀ q) * (Q - q))) +
      (1 - p) * (nsc_gc P.a₁ P.b₁ Q -
        (nsc_gc P.a₁ P.b₁ q - (1 - nsc_Fc P.a₁ P.b₁ q) * (Q - q))) := by
    intro Q
    rw [hS, hS]
    linear_combination (Q - q) * hF
  have hge : ∀ Q, P.supplierCost p q ≤ P.supplierCost p Q := by
    intro Q
    have := hdiff Q
    have u0 := (nsc_U P.a₀ P.b₀ q Q h0).1
    have u1 := (nsc_U P.a₁ P.b₁ q Q h1).1
    have : 0 ≤ p * (nsc_gc P.a₀ P.b₀ Q -
        (nsc_gc P.a₀ P.b₀ q - (1 - nsc_Fc P.a₀ P.b₀ q) * (Q - q))) :=
      mul_nonneg hp0 (by linarith)
    have : 0 ≤ (1 - p) * (nsc_gc P.a₁ P.b₁ Q -
        (nsc_gc P.a₁ P.b₁ q - (1 - nsc_Fc P.a₁ P.b₁ q) * (Q - q))) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hgt : ∀ Q, Q ≠ q → P.supplierCost p q < P.supplierCost p Q := by
    intro Q hne
    have := hdiff Q
    have u0 := nsc_U P.a₀ P.b₀ q Q h0
    have u1 := nsc_U P.a₁ P.b₁ q Q h1
    have n0 : 0 ≤ p * (nsc_gc P.a₀ P.b₀ Q -
        (nsc_gc P.a₀ P.b₀ q - (1 - nsc_Fc P.a₀ P.b₀ q) * (Q - q))) :=
      mul_nonneg hp0 (by linarith [u0.1])
    have n1 : 0 ≤ (1 - p) * (nsc_gc P.a₁ P.b₁ Q -
        (nsc_gc P.a₁ P.b₁ q - (1 - nsc_Fc P.a₁ P.b₁ q) * (Q - q))) :=
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

lemma nsc_Fc_lo (a b q : ℝ) (h : q ≤ a) : nsc_Fc a b q = 0 := by
  unfold nsc_Fc; rw [if_pos h]

lemma nsc_Fc_mid (a b q : ℝ) (hab : a < b) (h1 : a ≤ q) (h2 : q ≤ b) :
    nsc_Fc a b q = (q - a) / (b - a) := by
  unfold nsc_Fc
  by_cases h : q ≤ a
  · rw [if_pos h, show q = a by linarith]; simp
  · rw [if_neg h, if_pos h2]

lemma nsc_Fc_hi (a b q : ℝ) (hab : a < b) (h : b ≤ q) : nsc_Fc a b q = 1 := by
  unfold nsc_Fc
  rw [if_neg (by linarith)]
  by_cases h2 : q ≤ b
  · rw [if_pos h2, show q = b by linarith, div_self (by linarith)]
  · rw [if_neg h2]


theorem nsc_prop1 (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    (P.ξ ∈ Set.Icc (P.τup p) 1 →
      ∀ Q, P.IsOptimalQuantity p Q ↔ Q = P.b₀ - (P.b₀ - P.a₀) * (1 - P.ξ) / p) ∧
    (P.ξ ∈ Set.Icc (P.τlow p) (P.τup p) →
      ∀ Q, P.IsOptimalQuantity p Q ↔
        Q = (P.b₁ * (P.ξ - P.τlow p) + P.a₁ * (P.τup p - P.ξ)) / (P.τup p - P.τlow p)) ∧
    (P.ξ ∈ Set.Icc 0 (P.τlow p) →
      ∀ Q, P.IsOptimalQuantity p Q ↔ Q = P.ξ * (P.b₀ - P.a₀) / p + P.a₀) := by
  obtain ⟨hp0, hp1⟩ := hp
  have hL : 0 < P.b₀ - P.a₀ := by linarith
  have hl : 0 < P.b₁ - P.a₁ := by linarith
  refine ⟨fun ⟨hτ, _⟩ => ?_, fun ⟨hτl, hτu⟩ => ?_, fun ⟨_, hτ⟩ => ?_⟩
  · -- high regime
    unfold Params.τup at hτ
    have hτ' : (1 - P.ξ) * (P.b₀ - P.a₀) ≤ p * (P.b₀ - P.b₁) := by
      have : 1 - P.ξ ≤ p * (P.b₀ - P.b₁) / (P.b₀ - P.a₀) := by linarith
      rwa [le_div_iff₀ hL] at this
    have hpp : 0 < p := by
      rcases eq_or_lt_of_le hp0 with h | h
      · subst h; nlinarith
      · exact h
    set t := (P.b₀ - P.a₀) * (1 - P.ξ) / p with ht_def
    have ht : t * p = (P.b₀ - P.a₀) * (1 - P.ξ) := div_mul_cancel₀ _ hpp.ne'
    have htpos : 0 < t := by
      have : 0 < t * p := by rw [ht]; exact mul_pos hL (by linarith)
      exact pos_of_mul_pos_left this hpp.le
    have hthi : t ≤ P.b₀ - P.b₁ := by
      have : t * p ≤ (P.b₀ - P.b₁) * p := by rw [ht]; linarith
      exact le_of_mul_le_mul_right this hpp
    apply nsc_opt_iff P ha ha₁ p ⟨hp0, hp1⟩ _ (by linarith)
    · rw [nsc_Fc_mid _ _ _ ha (by linarith) (by linarith),
        nsc_Fc_hi _ _ _ ha₁ (by linarith)]
      field_simp
      linear_combination -ht
    · right; exact ⟨hpp, by linarith, by linarith⟩
  · -- middle regime
    have hA : P.τlow p = p * (P.a₁ - P.a₀) / (P.b₀ - P.a₀) := rfl
    have hB : P.τup p = 1 - p * (P.b₀ - P.b₁) / (P.b₀ - P.a₀) := rfl
    generalize P.τlow p = A at hA hτl ⊢
    generalize P.τup p = B at hB hτu ⊢
    have hNe : B - A = (P.b₀ - P.a₀ - p * (P.b₀ - P.a₀ - (P.b₁ - P.a₁))) / (P.b₀ - P.a₀) := by
      rw [hA, hB]; field_simp; ring
    have hNp : 0 < B - A := by
      rw [hNe]; apply div_pos _ hL; nlinarith
    have hA0 : 0 ≤ A := by rw [hA]; apply div_nonneg _ hL.le; nlinarith
    have hB1 : B ≤ 1 := by
      rw [hB]; have : 0 ≤ p * (P.b₀ - P.b₁) / (P.b₀ - P.a₀) := by
        apply div_nonneg _ hL.le; nlinarith
      linarith
    obtain ⟨t, ht⟩ : ∃ t, t = (P.ξ - A) / (B - A) := ⟨_, rfl⟩
    have htN : t * (B - A) = P.ξ - A := by rw [ht]; exact div_mul_cancel₀ _ hNp.ne'
    have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg (by linarith) hNp.le
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hNp]; linarith
    have hQ : (P.b₁ * (P.ξ - A) + P.a₁ * (B - P.ξ)) / (B - A) = P.a₁ + (P.b₁ - P.a₁) * t := by
      rw [ht]; field_simp; ring
    rw [hQ]
    have hlt : 0 ≤ (P.b₁ - P.a₁) * t := mul_nonneg hl.le ht0
    have hlt1 : (P.b₁ - P.a₁) * t ≤ P.b₁ - P.a₁ := by nlinarith
    apply nsc_opt_iff P ha ha₁ p ⟨hp0, hp1⟩ _ (by linarith)
    · rw [nsc_Fc_mid _ _ _ ha (by linarith) (by linarith),
        nsc_Fc_mid _ _ _ ha₁ (by linarith) (by linarith)]
      have key : p * ((P.a₁ + (P.b₁ - P.a₁) * t - P.a₀) / (P.b₀ - P.a₀)) +
          (1 - p) * ((P.a₁ + (P.b₁ - P.a₁) * t - P.a₁) / (P.b₁ - P.a₁)) = A + t * (B - A) := by
        rw [hNe, hA]; field_simp; ring
      rw [key, htN]; ring
    · rcases eq_or_lt_of_le hp0 with h | h
      · left
        subst h
        have hA' : A = 0 := by rw [hA]; simp
        have hB' : B = 1 := by rw [hB]; simp
        rw [hA', hB'] at htN
        have : t = P.ξ := by linarith
        rw [this]
        refine ⟨by norm_num, by nlinarith, by nlinarith⟩
      · right
        refine ⟨h, ?_, ?_⟩
        · by_contra hc
          have e1 : P.a₁ = P.a₀ := by nlinarith
          have e2 : (P.b₁ - P.a₁) * t = 0 := by linarith
          have e3 : t = 0 := by
            rcases mul_eq_zero.mp e2 with e | e
            · linarith
            · exact e
          rw [hA, e1, e3] at htN; simp at htN; linarith
        · by_contra hc
          have e1 : P.b₁ = P.b₀ := by nlinarith
          have e2 : t = 1 := by
            rcases eq_or_lt_of_le ht1 with e | e
            · exact e
            · exfalso; nlinarith
          rw [hB, hA, e1, e2] at htN; simp at htN; linarith
  · -- low regime
    unfold Params.τlow at hτ
    have hτ' : P.ξ * (P.b₀ - P.a₀) ≤ p * (P.a₁ - P.a₀) := by
      rwa [le_div_iff₀ hL] at hτ
    have hpp : 0 < p := by
      rcases eq_or_lt_of_le hp0 with h | h
      · subst h; nlinarith [mul_pos hξ0 hL]
      · exact h
    set t := P.ξ * (P.b₀ - P.a₀) / p with ht_def
    have ht : t * p = P.ξ * (P.b₀ - P.a₀) := div_mul_cancel₀ _ hpp.ne'
    have htpos : 0 < t := by positivity
    have hthi : t ≤ P.a₁ - P.a₀ := by
      have : t * p ≤ (P.a₁ - P.a₀) * p := by rw [ht]; linarith
      exact le_of_mul_le_mul_right this hpp
    apply nsc_opt_iff P ha ha₁ p ⟨hp0, hp1⟩ _ (by linarith)
    · rw [nsc_Fc_mid _ _ _ ha (by linarith) (by linarith),
        nsc_Fc_lo _ _ _ (by linarith)]
      field_simp
      linear_combination ht
    · right; exact ⟨hpp, by linarith, by linarith⟩

theorem solution (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    (P.ξ ∈ Set.Icc (P.τup p) 1 →
      ∀ Q, P.IsOptimalQuantity p Q ↔ Q = P.b₀ - (P.b₀ - P.a₀) * (1 - P.ξ) / p) ∧
    (P.ξ ∈ Set.Icc (P.τlow p) (P.τup p) →
      ∀ Q, P.IsOptimalQuantity p Q ↔
        Q = (P.b₁ * (P.ξ - P.τlow p) + P.a₁ * (P.τup p - P.ξ)) / (P.τup p - P.τlow p)) ∧
    (P.ξ ∈ Set.Icc 0 (P.τlow p) →
      ∀ Q, P.IsOptimalQuantity p Q ↔ Q = P.ξ * (P.b₀ - P.a₀) / p + P.a₀) :=
  nsc_prop1 P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b p hp
