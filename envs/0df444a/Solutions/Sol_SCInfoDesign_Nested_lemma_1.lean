-- Prove2me | solution 1 for SCInfoDesign.Nested.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T19:19:29.571573+00:00
-- url     : https://prove2.me/submissions/b42ef9f5-bab8-4b22-8316-68c33e60a2c8

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

open BiconvexProg.BranchBound


lemma nsc_uniq (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    ∀ Q, P.IsOptimalQuantity p Q ↔ Q = P.prefQ p := by
  obtain ⟨h1, h2', h3⟩ := nsc_prop1 P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b p hp
  have key : ∃ q, ∀ Q, P.IsOptimalQuantity p Q ↔ Q = q := by
    by_cases c1 : P.τup p ≤ P.ξ
    · exact ⟨_, h1 ⟨c1, hξ1.le⟩⟩
    by_cases c2 : P.τlow p ≤ P.ξ
    · exact ⟨_, h2' ⟨c2, le_of_lt (not_le.mp c1)⟩⟩
    exact ⟨_, h3 ⟨hξ0.le, le_of_lt (not_le.mp c2)⟩⟩
  obtain ⟨q, hq⟩ := key
  have hset : {Q | P.IsOptimalQuantity p Q} = {q} := Set.ext fun Q => hq Q
  have : P.prefQ p = q := by
    show sSup {Q | P.IsOptimalQuantity p Q} = q
    rw [hset, csSup_singleton]
  rw [this]; exact hq

lemma nsc_K_nonneg (P : Params) (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) : 0 ≤ P.K p := by
  obtain ⟨hp0, hp1⟩ := hp
  have gnn : ∀ a b Q : ℝ, a < b → 0 ≤ nsc_gc a b Q := by
    intro a b Q hab
    unfold nsc_gc
    split_ifs with h1 h2
    · linarith
    · have : 0 < b - a := by linarith
      positivity
    · rfl
  unfold Params.K Params.retailerCost
  rw [nsc_mean_pos _ _ _ (by linarith), nsc_mean_pos _ _ _ (by linarith)]
  have := gnn P.a₀ P.b₀ (P.prefQ p) (by linarith)
  have := gnn P.a₁ P.b₁ (P.prefQ p) (by linarith)
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- splittings of a prior `x` into finitely many posteriors -/
def nsc_Split (x : ℝ) (n : ℕ) (w q : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, q i ∈ Set.Icc (0:ℝ) 1) ∧ ∑ i, w i * q i = x

def nsc_A (P : Params) (x : ℝ) : Set ℝ :=
  {v | ∃ (n : ℕ) (w q : Fin n → ℝ), nsc_Split x n w q ∧ v = ∑ i, w i * P.K (q i)}

noncomputable def nsc_h (P : Params) (x : ℝ) : ℝ := sInf (nsc_A P x)

lemma nsc_A_nonneg (P : Params) (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁)
    (x v : ℝ) (hv : v ∈ nsc_A P x) : 0 ≤ v := by
  obtain ⟨n, w, q, ⟨hw, -, hq, -⟩, rfl⟩ := hv
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (nsc_K_nonneg P ha ha₁ _ (hq i))

lemma nsc_A_trivial (P : Params) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    P.K x ∈ nsc_A P x :=
  ⟨1, fun _ => 1, fun _ => x, ⟨fun _ => zero_le_one, by simp, fun _ => hx, by simp⟩, by simp⟩

lemma nsc_h_le_K (P : Params) (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁)
    (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) : nsc_h P x ≤ P.K x :=
  csInf_le ⟨0, fun v hv => nsc_A_nonneg P ha ha₁ x v hv⟩ (nsc_A_trivial P x hx)

lemma nsc_A_comb (P : Params) (x y a b u v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hu : u ∈ nsc_A P x) (hv : v ∈ nsc_A P y) : a * u + b * v ∈ nsc_A P (a * x + b * y) := by
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

lemma nsc_h_convex (P : Params) (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) :
    ConvexOn ℝ (Set.Icc (0:ℝ) 1) (nsc_h P) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha0 hb0 hab
  simp only [smul_eq_mul]
  have bddA : ∀ z, BddBelow (nsc_A P z) := fun z => ⟨0, fun v hv => nsc_A_nonneg P ha ha₁ z v hv⟩
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨u, hu, hu'⟩ := exists_lt_of_csInf_lt ⟨_, nsc_A_trivial P x hx⟩
    (lt_add_of_pos_right (nsc_h P x) hε)
  obtain ⟨v, hv, hv'⟩ := exists_lt_of_csInf_lt ⟨_, nsc_A_trivial P y hy⟩
    (lt_add_of_pos_right (nsc_h P y) hε)
  have hmem := nsc_A_comb P x y a b u v ha0 hb0 hab hu hv
  have h1 : nsc_h P (a * x + b * y) ≤ a * u + b * v := csInf_le (bddA _) hmem
  have h2 : a * u ≤ a * (nsc_h P x + ε) := mul_le_mul_of_nonneg_left hu'.le ha0
  have h3 : b * v ≤ b * (nsc_h P y + ε) := mul_le_mul_of_nonneg_left hv'.le hb0
  -- strictness: at least one of a, b is positive
  rcases eq_or_lt_of_le ha0 with ha' | ha'
  · have h3' : b * v < b * (nsc_h P y + ε) := mul_lt_mul_of_pos_left hv' (by linarith)
    nlinarith
  · have h2' : a * u < a * (nsc_h P x + ε) := mul_lt_mul_of_pos_left hu' ha'
    nlinarith

lemma nsc_realize (P : Params) (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0:ℝ) 1) (n : ℕ)
    (w q : Fin n → ℝ) (hs : nsc_Split p₀ n w q) :
    ∃ π : Fin 2 → Fin n → ℝ, SCInfoDesign.Nested.IsPolicy π ∧
      P.expectedCost p₀ π P.prefQ = ∑ i, w i * P.K (q i) := by
  obtain ⟨hp0, hp1⟩ := hp₀
  obtain ⟨hw, hw1, hq, hwq⟩ := hs
  have hwq_nn : ∀ i, 0 ≤ w i * q i := fun i => mul_nonneg (hw i) (hq i).1
  have hw1q_nn : ∀ i, 0 ≤ w i * (1 - q i) := fun i => mul_nonneg (hw i) (by linarith [(hq i).2])
  have hsum1q : ∑ i, w i * (1 - q i) = 1 - p₀ := by
    simp_rw [mul_sub, mul_one]; rw [Finset.sum_sub_distrib, hw1, hwq]
  let π : Fin 2 → Fin n → ℝ := ![fun i => if p₀ = 0 then w i else w i * q i / p₀,
    fun i => if p₀ = 1 then w i else w i * (1 - q i) / (1 - p₀)]
  have hπ0 : ∀ i, π 0 i = if p₀ = 0 then w i else w i * q i / p₀ := fun i => rfl
  have hπ1 : ∀ i, π 1 i = if p₀ = 1 then w i else w i * (1 - q i) / (1 - p₀) := fun i => rfl
  -- probability of each message is w i
  have hmsg : ∀ i, SCInfoDesign.Nested.msgProb p₀ π i = w i := by
    intro i
    unfold SCInfoDesign.Nested.msgProb
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
  · unfold Params.expectedCost
    apply Finset.sum_congr rfl
    intro i _
    rw [hmsg i]
    show w i * P.K (SCInfoDesign.Nested.posterior p₀ π i) = w i * P.K (q i)
    by_cases hwi : w i = 0
    · rw [hwi]; ring
    congr 2
    unfold SCInfoDesign.Nested.posterior
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

theorem nsc_value (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0:ℝ) 1) :
    IsGLB {c : ℝ | ∃ (n : ℕ) (π : Fin 2 → Fin n → ℝ) (Qs : ℝ → ℝ),
        SCInfoDesign.Nested.IsPolicy π ∧ P.IsBestResponseProfile Qs ∧ c = P.expectedCost p₀ π Qs}
      (convexEnvelope (Set.Icc (0:ℝ) 1) P.K p₀) := by
  obtain ⟨hp0, hp1⟩ := hp₀
  -- the set of values of convex minorants at p₀
  have hG_bdd : BddAbove {r : ℝ | ∃ g : ℝ → ℝ, ConvexOn ℝ (Set.Icc (0:ℝ) 1) g ∧
      (∀ w ∈ Set.Icc (0:ℝ) 1, g w ≤ P.K w) ∧ r = g p₀} := by
    refine ⟨P.K p₀, ?_⟩
    rintro r ⟨g, -, hg, rfl⟩
    exact hg p₀ ⟨hp0, hp1⟩
  have hG_ne : Set.Nonempty {r : ℝ | ∃ g : ℝ → ℝ, ConvexOn ℝ (Set.Icc (0:ℝ) 1) g ∧
      (∀ w ∈ Set.Icc (0:ℝ) 1, g w ≤ P.K w) ∧ r = g p₀} :=
    ⟨0, fun _ => 0, convexOn_const 0 (convex_Icc 0 1),
      fun w hw => nsc_K_nonneg P ha ha₁ w hw, rfl⟩
  constructor
  · -- lower bound
    rintro c ⟨n, π, Qs, hπ, hQs, rfl⟩
    unfold convexEnvelope
    apply csSup_le hG_ne
    rintro r ⟨g, hg, hgK, rfl⟩
    set w : Fin n → ℝ := fun m => SCInfoDesign.Nested.msgProb p₀ π m with hw_def
    set q : Fin n → ℝ := fun m => SCInfoDesign.Nested.posterior p₀ π m with hq_def
    have hwnn : ∀ m, 0 ≤ w m := fun m => by
      simp only [hw_def, SCInfoDesign.Nested.msgProb]
      have := hπ.1 0 m; have := hπ.1 1 m
      have : 0 ≤ 1 - p₀ := by linarith
      positivity
    have hw1 : ∑ m, w m = 1 := by
      simp only [hw_def, SCInfoDesign.Nested.msgProb]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hπ.2 0, hπ.2 1]; ring
    have hwq : ∀ m, w m * q m = p₀ * π 0 m := by
      intro m
      simp only [hw_def, hq_def, SCInfoDesign.Nested.posterior]
      by_cases h : SCInfoDesign.Nested.msgProb p₀ π m = 0
      · rw [h]
        have a1 : 0 ≤ p₀ * π 0 m := mul_nonneg hp0 (hπ.1 0 m)
        have a2 : 0 ≤ (1 - p₀) * π 1 m := mul_nonneg (by linarith) (hπ.1 1 m)
        unfold SCInfoDesign.Nested.msgProb at h
        rw [zero_mul]; linarith
      · field_simp
    have hqI : ∀ m, q m ∈ Set.Icc (0:ℝ) 1 := by
      intro m
      simp only [hq_def, SCInfoDesign.Nested.posterior, SCInfoDesign.Nested.msgProb]
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
    unfold Params.expectedCost
    apply Finset.sum_le_sum
    intro m _
    have hQ : Qs (q m) = P.prefQ (q m) :=
      (nsc_uniq P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b (q m) (hqI m) _).1 (hQs (q m) (hqI m))
    show w m * g (q m) ≤ w m * P.retailerCost (q m) (Qs (q m))
    rw [hQ]
    exact mul_le_mul_of_nonneg_left (hgK _ (hqI m)) (hwnn m)
  · -- greatest lower bound
    intro c hc
    have hBR : P.IsBestResponseProfile P.prefQ := fun p hp =>
      (nsc_uniq P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b p hp _).2 rfl
    have h1 : c ≤ nsc_h P p₀ := by
      apply le_csInf ⟨_, nsc_A_trivial P p₀ ⟨hp0, hp1⟩⟩
      rintro v ⟨n, w, q, hs, rfl⟩
      obtain ⟨π, hπ, hcost⟩ := nsc_realize P p₀ ⟨hp0, hp1⟩ n w q hs
      rw [← hcost]
      exact hc ⟨n, π, P.prefQ, hπ, hBR, rfl⟩
    refine le_trans h1 ?_
    unfold convexEnvelope
    apply le_csSup hG_bdd
    exact ⟨nsc_h P, nsc_h_convex P ha ha₁, fun w hw => nsc_h_le_K P ha ha₁ w hw, rfl⟩

lemma nsc_prefQ_eq (P : Params) (p q : ℝ) (h : ∀ Q, P.IsOptimalQuantity p Q ↔ Q = q) :
    P.prefQ p = q := by
  have hset : {Q | P.IsOptimalQuantity p Q} = {q} := Set.ext fun Q => h Q
  show sSup {Q | P.IsOptimalQuantity p Q} = q
  rw [hset, csSup_singleton]

lemma nsc_gc_lo (a b Q : ℝ) (h : Q ≤ a) : nsc_gc a b Q = (a + b) / 2 - Q := by
  unfold nsc_gc; rw [if_pos h]

lemma nsc_gc_mid (a b Q : ℝ) (hab : a < b) (h1 : a ≤ Q) (h2 : Q ≤ b) :
    nsc_gc a b Q = (b - Q) ^ 2 / (2 * (b - a)) := by
  unfold nsc_gc
  by_cases h : Q ≤ a
  · rw [if_pos h, show Q = a by linarith]
    field_simp [show b - a ≠ 0 by linarith]; ring
  · rw [if_neg h, if_pos h2]

lemma nsc_gc_hi (a b Q : ℝ) (hab : a < b) (h : b ≤ Q) : nsc_gc a b Q = 0 := by
  unfold nsc_gc
  rw [if_neg (by linarith)]
  by_cases h2 : Q ≤ b
  · rw [if_pos h2, show Q = b by linarith]; simp
  · rw [if_neg h2]

lemma nsc_K_eq (P : Params) (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁)
    (x : ℝ) : P.K x = x * nsc_gc P.a₀ P.b₀ (P.prefQ x) +
      (1 - x) * nsc_gc P.a₁ P.b₁ (P.prefQ x) := by
  unfold Params.K Params.retailerCost
  rw [nsc_mean_pos _ _ _ ha, nsc_mean_pos _ _ _ ha₁]

/-- the middle-regime quantity lies in `[a₁, b₁]` -/
lemma nsc_Qmid_mem (P : Params) (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (hτl : P.τlow p ≤ P.ξ) (hτu : P.ξ ≤ P.τup p) :
    P.a₁ ≤ (P.b₁ * (P.ξ - P.τlow p) + P.a₁ * (P.τup p - P.ξ)) / (P.τup p - P.τlow p) ∧
    (P.b₁ * (P.ξ - P.τlow p) + P.a₁ * (P.τup p - P.ξ)) / (P.τup p - P.τlow p) ≤ P.b₁ := by
  obtain ⟨hp0, hp1⟩ := hp
  have hL : 0 < P.b₀ - P.a₀ := by linarith
  have hl : 0 < P.b₁ - P.a₁ := by linarith
  have hA : P.τlow p = p * (P.a₁ - P.a₀) / (P.b₀ - P.a₀) := rfl
  have hB : P.τup p = 1 - p * (P.b₀ - P.b₁) / (P.b₀ - P.a₀) := rfl
  generalize P.τlow p = A at hA hτl ⊢
  generalize P.τup p = B at hB hτu ⊢
  have hNe : B - A = (P.b₀ - P.a₀ - p * (P.b₀ - P.a₀ - (P.b₁ - P.a₁))) / (P.b₀ - P.a₀) := by
    rw [hA, hB]; field_simp; ring
  have hNp : 0 < B - A := by
    rw [hNe]; apply div_pos _ hL; nlinarith
  constructor
  · rw [le_div_iff₀ hNp]; nlinarith
  · rw [div_le_iff₀ hNp]; nlinarith

lemma nsc_K_midQ (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (hτl : P.τlow p ≤ P.ξ) (hτu : P.ξ ≤ P.τup p) :
    P.K p =
        p / (P.b₀ - P.a₀) *
            (P.b₀ - (P.b₁ * (P.ξ - P.τlow p) + P.a₁ * (P.τup p - P.ξ)) / (P.τup p - P.τlow p)) ^ 2 / 2 +
          (1 - p) / (P.b₁ - P.a₁) *
            (P.b₁ - (P.b₁ * (P.ξ - P.τlow p) + P.a₁ * (P.τup p - P.ξ)) / (P.τup p - P.τlow p)) ^ 2 / 2 := by
  have hq := nsc_prefQ_eq P p _
    ((nsc_prop1 P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b p hp).2.1 ⟨hτl, hτu⟩)
  obtain ⟨h1, h2⟩ := nsc_Qmid_mem P ha ha₁ hnest_a hnest_b p hp hτl hτu
  rw [nsc_K_eq P ha ha₁, hq, nsc_gc_mid _ _ _ ha (by linarith) (by linarith),
    nsc_gc_mid _ _ _ ha₁ h1 h2]
  have : P.b₀ - P.a₀ ≠ 0 := by linarith
  have : P.b₁ - P.a₁ ≠ 0 := by linarith
  field_simp

lemma nsc_K_lowQ (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (hτ : P.ξ ≤ P.τlow p) :
    P.K p =
        p / (P.b₀ - P.a₀) * (P.b₀ - (P.ξ * (P.b₀ - P.a₀) / p + P.a₀)) ^ 2 / 2 +
          (1 - p) * ((P.b₁ + P.a₁) / 2 - (P.ξ * (P.b₀ - P.a₀) / p + P.a₀)) := by
  have hq := nsc_prefQ_eq P p _
    ((nsc_prop1 P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b p hp).2.2 ⟨hξ0.le, hτ⟩)
  obtain ⟨hp0, hp1⟩ := hp
  have hL : 0 < P.b₀ - P.a₀ := by linarith
  unfold Params.τlow at hτ
  have hτ' : P.ξ * (P.b₀ - P.a₀) ≤ p * (P.a₁ - P.a₀) := by
    rwa [le_div_iff₀ hL] at hτ
  have hpp : 0 < p := by
    rcases eq_or_lt_of_le hp0 with h | h
    · subst h; nlinarith [mul_pos hξ0 hL]
    · exact h
  have ht : P.ξ * (P.b₀ - P.a₀) / p * p = P.ξ * (P.b₀ - P.a₀) := div_mul_cancel₀ _ hpp.ne'
  have htpos : 0 < P.ξ * (P.b₀ - P.a₀) / p := by positivity
  have hthi : P.ξ * (P.b₀ - P.a₀) / p ≤ P.a₁ - P.a₀ := by
    have : P.ξ * (P.b₀ - P.a₀) / p * p ≤ (P.a₁ - P.a₀) * p := by rw [ht]; linarith
    exact le_of_mul_le_mul_right this hpp
  rw [nsc_K_eq P ha ha₁, hq, nsc_gc_mid _ _ _ ha (by linarith) (by linarith),
    nsc_gc_lo _ _ _ (by linarith)]
  have : P.b₀ - P.a₀ ≠ 0 := by linarith
  field_simp
  ring

lemma nsc_K_high (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (hτ : P.τup p ≤ P.ξ) :
    P.K p = (1 - P.ξ) ^ 2 * (P.b₀ - P.a₀) / (2 * p) := by
  have hq := nsc_prefQ_eq P p _
    ((nsc_prop1 P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b p hp).1 ⟨hτ, hξ1.le⟩)
  obtain ⟨hp0, hp1⟩ := hp
  have hL : 0 < P.b₀ - P.a₀ := by linarith
  unfold Params.τup at hτ
  have hτ' : (1 - P.ξ) * (P.b₀ - P.a₀) ≤ p * (P.b₀ - P.b₁) := by
    have : 1 - P.ξ ≤ p * (P.b₀ - P.b₁) / (P.b₀ - P.a₀) := by linarith
    rwa [le_div_iff₀ hL] at this
  have hpp : 0 < p := by
    rcases eq_or_lt_of_le hp0 with h | h
    · subst h; nlinarith
    · exact h
  have ht : (P.b₀ - P.a₀) * (1 - P.ξ) / p * p = (P.b₀ - P.a₀) * (1 - P.ξ) :=
    div_mul_cancel₀ _ hpp.ne'
  have htpos : 0 < (P.b₀ - P.a₀) * (1 - P.ξ) / p := by
    apply div_pos (mul_pos hL (by linarith)) hpp
  have hthi : (P.b₀ - P.a₀) * (1 - P.ξ) / p ≤ P.b₀ - P.b₁ := by
    have : (P.b₀ - P.a₀) * (1 - P.ξ) / p * p ≤ (P.b₀ - P.b₁) * p := by rw [ht]; linarith
    exact le_of_mul_le_mul_right this hpp
  rw [nsc_K_eq P ha ha₁, hq, nsc_gc_mid _ _ _ ha (by linarith) (by linarith),
    nsc_gc_hi _ _ _ ha₁ (by linarith)]
  have : P.b₀ - P.a₀ ≠ 0 := by linarith
  field_simp
  ring

lemma nsc_regimes (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (hξ_le : P.ξ ≤ (P.a₁ - P.a₀) / (P.b₀ - P.a₀))
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    0 < P.a₁ - P.a₀ ∧ (p ≤ P.pHat → P.τlow p ≤ P.ξ ∧ P.ξ ≤ P.τup p) ∧
      (P.pHat ≤ p → P.ξ ≤ P.τlow p) := by
  obtain ⟨hp0, hp1⟩ := hp
  have hL : 0 < P.b₀ - P.a₀ := by linarith
  have hξ' : P.ξ * (P.b₀ - P.a₀) ≤ P.a₁ - P.a₀ := by rwa [le_div_iff₀ hL] at hξ_le
  have hα : 0 < P.a₁ - P.a₀ := by nlinarith [mul_pos hξ0 hL]
  refine ⟨hα, fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · unfold Params.pHat at h
    rw [le_div_iff₀ hα] at h
    unfold Params.τlow
    rw [div_le_iff₀ hL]; linarith
  · unfold Params.τup
    have : p * (P.b₀ - P.b₁) / (P.b₀ - P.a₀) ≤ 1 - P.ξ := by
      rw [div_le_iff₀ hL]; nlinarith
    linarith
  · unfold Params.pHat at h
    rw [div_le_iff₀ hα] at h
    unfold Params.τlow
    rw [le_div_iff₀ hL]; linarith

theorem nsc_eq_B5 (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (hξ_le : P.ξ ≤ (P.a₁ - P.a₀) / (P.b₀ - P.a₀))
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    (p ≤ P.pHat →
      P.K p =
        p / (P.b₀ - P.a₀) *
            (P.b₀ - (P.b₁ * (P.ξ - P.τlow p) + P.a₁ * (P.τup p - P.ξ)) / (P.τup p - P.τlow p)) ^ 2 / 2 +
          (1 - p) / (P.b₁ - P.a₁) *
            (P.b₁ - (P.b₁ * (P.ξ - P.τlow p) + P.a₁ * (P.τup p - P.ξ)) / (P.τup p - P.τlow p)) ^ 2 / 2) ∧
    (P.pHat ≤ p →
      P.K p =
        p / (P.b₀ - P.a₀) * (P.b₀ - (P.ξ * (P.b₀ - P.a₀) / p + P.a₀)) ^ 2 / 2 +
          (1 - p) * ((P.b₁ + P.a₁) / 2 - (P.ξ * (P.b₀ - P.a₀) / p + P.a₀))) := by
  obtain ⟨_, h1, h2⟩ := nsc_regimes P ha ha₁ hξ0 hξ1 hnest_a hnest_b hξ_le p hp
  exact ⟨fun h => nsc_K_midQ P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b p hp (h1 h).1 (h1 h).2,
    fun h => nsc_K_lowQ P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b p hp (h2 h)⟩

/-! ### Closed forms of `K` and the algebraic identities behind Lemma 1 -/

noncomputable def nsc_nM (a0 b0 a1 b1 ξ x : ℝ) : ℝ :=
  (b1 - a1) * ((1 - ξ) ^ 2 * (b0 - a0) ^ 2 - x ^ 2 * (b0 - b1) ^ 2) /
      (2 * (b0 - a0) * ((b0 - a0) - x * ((a1 - a0) + (b0 - b1)))) +
    x * (b0 - b1) ^ 2 / (2 * (b0 - a0))

noncomputable def nsc_nLo (a0 b0 a1 b1 ξ x : ℝ) : ℝ :=
  (2 * (a1 - a0) - (a1 - a0) * x + (b0 - b1) * x + (b1 - a1)) / 2 -
    ξ * (2 - ξ) * (b0 - a0) / (2 * x)

noncomputable def nsc_nHi (a0 b0 ξ x : ℝ) : ℝ := (1 - ξ) ^ 2 * (b0 - a0) / (2 * x)

lemma nsc_alg_mid (a0 b0 a1 b1 ξ x : ℝ) (hL : 0 < b0 - a0) (hl : 0 < b1 - a1)
    (hD : 0 < (b0 - a0) - x * ((a1 - a0) + (b0 - b1))) :
    x / (b0 - a0) * (b0 - (b1 * (ξ - x * (a1 - a0) / (b0 - a0)) +
        a1 * ((1 - x * (b0 - b1) / (b0 - a0)) - ξ)) /
        ((1 - x * (b0 - b1) / (b0 - a0)) - x * (a1 - a0) / (b0 - a0))) ^ 2 / 2 +
      (1 - x) / (b1 - a1) * (b1 - (b1 * (ξ - x * (a1 - a0) / (b0 - a0)) +
        a1 * ((1 - x * (b0 - b1) / (b0 - a0)) - ξ)) /
        ((1 - x * (b0 - b1) / (b0 - a0)) - x * (a1 - a0) / (b0 - a0))) ^ 2 / 2 =
    nsc_nM a0 b0 a1 b1 ξ x := by
  have hBA : (1 - x * (b0 - b1) / (b0 - a0)) - x * (a1 - a0) / (b0 - a0) =
      ((b0 - a0) - x * ((a1 - a0) + (b0 - b1))) / (b0 - a0) := by
    field_simp; ring
  have hQ : (b1 * (ξ - x * (a1 - a0) / (b0 - a0)) + a1 * ((1 - x * (b0 - b1) / (b0 - a0)) - ξ)) /
      ((1 - x * (b0 - b1) / (b0 - a0)) - x * (a1 - a0) / (b0 - a0)) =
      a1 + (b1 - a1) * (ξ * (b0 - a0) - x * (a1 - a0)) /
        ((b0 - a0) - x * ((a1 - a0) + (b0 - b1))) := by
    rw [hBA]; field_simp; ring
  rw [hQ]
  unfold nsc_nM
  field_simp
  ring

lemma nsc_alg_low (a0 b0 a1 b1 ξ x : ℝ) (hL : 0 < b0 - a0) (hx : 0 < x) :
    x / (b0 - a0) * (b0 - (ξ * (b0 - a0) / x + a0)) ^ 2 / 2 +
      (1 - x) * ((b1 + a1) / 2 - (ξ * (b0 - a0) / x + a0)) = nsc_nLo a0 b0 a1 b1 ξ x := by
  unfold nsc_nLo
  field_simp
  ring

lemma nsc_d1 (a0 b0 a1 b1 ξ x : ℝ) (hL : b0 - a0 ≠ 0)
    (hD : (b0 - a0) - x * ((a1 - a0) + (b0 - b1)) ≠ 0) :
    nsc_nM a0 b0 a1 b1 ξ x - (x * ((1 - ξ) ^ 2 * (b0 - a0) / 2) + (1 - x) * ((1 - ξ) ^ 2 * (b1 - a1) / 2)) =
      x * (1 - x) * (ξ * ((a1 - a0) + (b0 - b1)) - (a1 - a0)) *
        ((a1 - a0) + 2 * (b0 - b1) - ξ * ((a1 - a0) + (b0 - b1))) /
        (2 * ((b0 - a0) - x * ((a1 - a0) + (b0 - b1)))) := by
  unfold nsc_nM
  field_simp
  ring

lemma nsc_d2 (a0 b0 a1 b1 ξ x : ℝ) (hx : x ≠ 0) :
    nsc_nHi a0 b0 ξ x - (x * ((1 - ξ) ^ 2 * (b0 - a0) / 2) + (1 - x) * ((1 - ξ) ^ 2 * (b1 - a1) / 2)) =
      (1 - x) * (1 - ξ) ^ 2 * ((b0 - a0) + x * ((a1 - a0) + (b0 - b1))) / (2 * x) := by
  unfold nsc_nHi
  field_simp
  ring

lemma nsc_d3 (a0 b0 a1 b1 ξ x : ℝ) (hL : b0 - a0 ≠ 0) (hx : x ≠ 0)
    (hD : (b0 - a0) - x * ((a1 - a0) + (b0 - b1)) ≠ 0) :
    nsc_nLo a0 b0 a1 b1 ξ x - nsc_nM a0 b0 a1 b1 ξ x =
      (1 - x) * ((a1 - a0) * x - ξ * (b0 - a0)) * (2 * (b0 - a0) - (a1 - a0) * x - ξ * (b0 - a0)) /
        (2 * x * ((b0 - a0) - x * ((a1 - a0) + (b0 - b1)))) := by
  unfold nsc_nLo nsc_nM
  field_simp
  ring

lemma nsc_d4 (a0 b0 a1 b1 h x : ℝ) (hL : b0 - a0 ≠ 0) (hx : x ≠ 0) (h1 : 1 - h ≠ 0)
    (hDh : (b0 - a0) - h * ((a1 - a0) + (b0 - b1)) ≠ 0) :
    nsc_nLo a0 b0 a1 b1 (h * (a1 - a0) / (b0 - a0)) x -
      (((1 - h * (a1 - a0) / (b0 - a0)) ^ 2 * (b0 - a0) / 2 -
          nsc_nM a0 b0 a1 b1 (h * (a1 - a0) / (b0 - a0)) h) / (1 - h) * (x - h) +
        nsc_nM a0 b0 a1 b1 (h * (a1 - a0) / (b0 - a0)) h) =
      (1 - x) * (2 - h * (a1 - a0) / (b0 - a0)) * ((a1 - a0) * (x - h)) / (2 * x) := by
  unfold nsc_nLo nsc_nM
  field_simp
  ring

lemma nsc_d5 (a0 b0 a1 b1 h x : ℝ) (hL : b0 - a0 ≠ 0) (h1 : 1 - h ≠ 0)
    (hDh : (b0 - a0) - h * ((a1 - a0) + (b0 - b1)) ≠ 0)
    (hD : (b0 - a0) - x * ((a1 - a0) + (b0 - b1)) ≠ 0) :
    nsc_nM a0 b0 a1 b1 (h * (a1 - a0) / (b0 - a0)) x -
      (((1 - h * (a1 - a0) / (b0 - a0)) ^ 2 * (b0 - a0) / 2 -
          nsc_nM a0 b0 a1 b1 (h * (a1 - a0) / (b0 - a0)) h) / (1 - h) * (x - h) +
        nsc_nM a0 b0 a1 b1 (h * (a1 - a0) / (b0 - a0)) h) =
      (1 - x) * ((a1 - a0) * (x - h)) *
        (h * (a1 - a0) / (b0 - a0) * ((a1 - a0) + (b0 - b1)) - (a1 - a0) - 2 * (b0 - b1)) /
        (2 * ((b0 - a0) - x * ((a1 - a0) + (b0 - b1)))) := by
  unfold nsc_nM
  field_simp
  ring

lemma nsc_dec (a0 b0 a1 b1 ξ x : ℝ) (hL : b0 - a0 ≠ 0) (hs : (a1 - a0) + (b0 - b1) ≠ 0)
    (hD : (b0 - a0) - x * ((a1 - a0) + (b0 - b1)) ≠ 0) :
    nsc_nM a0 b0 a1 b1 ξ x =
      (b0 - b1) ^ 2 * (b1 - a1) / (2 * ((a1 - a0) + (b0 - b1)) ^ 2) +
        (b0 - b1) ^ 2 / (2 * ((a1 - a0) + (b0 - b1))) * x +
        (b0 - a0) * (b1 - a1) * ((a1 - a0) - ξ * ((a1 - a0) + (b0 - b1))) *
            ((1 - ξ) * ((a1 - a0) + (b0 - b1)) + (b0 - b1)) /
            (2 * ((a1 - a0) + (b0 - b1)) ^ 2) *
          (1 / ((b0 - a0) - x * ((a1 - a0) + (b0 - b1)))) := by
  unfold nsc_nM
  field_simp
  ring

lemma nsc_D_pos (P : Params) (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    0 < (P.b₀ - P.a₀) - x * ((P.a₁ - P.a₀) + (P.b₀ - P.b₁)) := by
  obtain ⟨hx0, hx1⟩ := hx
  have : x * ((P.a₁ - P.a₀) + (P.b₀ - P.b₁)) ≤ (P.a₁ - P.a₀) + (P.b₀ - P.b₁) := by
    have : 0 ≤ (P.a₁ - P.a₀) + (P.b₀ - P.b₁) := by linarith
    nlinarith
  linarith

lemma nsc_Kmid (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) (hτl : P.τlow x ≤ P.ξ) (hτu : P.ξ ≤ P.τup x) :
    P.K x = nsc_nM P.a₀ P.b₀ P.a₁ P.b₁ P.ξ x := by
  rw [nsc_K_midQ P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b x hx hτl hτu]
  simp only [Params.τlow, Params.τup]
  exact nsc_alg_mid _ _ _ _ _ _ (by linarith) (by linarith)
    (nsc_D_pos P ha ha₁ hnest_a hnest_b x hx)

lemma nsc_Klow (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) (hτ : P.ξ ≤ P.τlow x) :
    P.K x = nsc_nLo P.a₀ P.b₀ P.a₁ P.b₁ P.ξ x := by
  have hL : 0 < P.b₀ - P.a₀ := by linarith
  have hxp : 0 < x := by
    rcases eq_or_lt_of_le hx.1 with h | h
    · exfalso; rw [← h] at hτ; unfold Params.τlow at hτ; simp at hτ; linarith
    · exact h
  rw [nsc_K_lowQ P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b x hx hτ]
  exact nsc_alg_low _ _ _ _ _ _ hL hxp

lemma nsc_inv_comb (Y Z a b : ℝ) (hY : 0 < Y) (hZ : 0 < Z) (ha : 0 ≤ a) (hb : 0 ≤ b)
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

lemma nsc_affine_convex (u v : ℝ) : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun x => u + v * x) := by
  refine ⟨convex_Icc 0 1, fun x _ y _ a b _ _ hab => le_of_eq ?_⟩
  simp only [smul_eq_mul]
  linear_combination (-u) * hab

lemma nsc_nM_convex (P : Params) (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀) (hξ1 : P.ξ < 1)
    (hs : 0 < (P.a₁ - P.a₀) + (P.b₀ - P.b₁))
    (hξs : P.ξ * ((P.a₁ - P.a₀) + (P.b₀ - P.b₁)) ≤ P.a₁ - P.a₀) :
    ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun x => nsc_nM P.a₀ P.b₀ P.a₁ P.b₁ P.ξ x) := by
  have hL : 0 < P.b₀ - P.a₀ := by linarith
  have hl : 0 < P.b₁ - P.a₁ := by linarith
  set s := (P.a₁ - P.a₀) + (P.b₀ - P.b₁) with hs_def
  set C := (P.b₀ - P.a₀) * (P.b₁ - P.a₁) * ((P.a₁ - P.a₀) - P.ξ * s) *
      ((1 - P.ξ) * s + (P.b₀ - P.b₁)) / (2 * s ^ 2) with hC_def
  set c0 := (P.b₀ - P.b₁) ^ 2 * (P.b₁ - P.a₁) / (2 * s ^ 2)
  set c1 := (P.b₀ - P.b₁) ^ 2 / (2 * s)
  have hCnn : 0 ≤ C := by
    rw [hC_def]
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (mul_nonneg (mul_nonneg hL.le hl.le) (by linarith))
    have : 0 ≤ (1 - P.ξ) * s := mul_nonneg (by linarith) hs.le
    linarith
  have hNpos : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < (P.b₀ - P.a₀) - x * s :=
    fun x hx => nsc_D_pos P ha ha₁ hnest_a hnest_b x hx
  have hdec : ∀ x ∈ Set.Icc (0:ℝ) 1, nsc_nM P.a₀ P.b₀ P.a₁ P.b₁ P.ξ x =
      c0 + c1 * x + C * (1 / ((P.b₀ - P.a₀) - x * s)) := fun x hx =>
    nsc_dec _ _ _ _ _ _ hL.ne' hs.ne' (hNpos x hx).ne'
  refine ⟨convex_Icc 0 1, fun y hy z hz a b ha0 hb0 hab => ?_⟩
  have hyz : a • y + b • z ∈ Set.Icc (0:ℝ) 1 := (convex_Icc 0 1) hy hz ha0 hb0 hab
  simp only [smul_eq_mul] at hyz ⊢
  rw [hdec _ hyz, hdec _ hy, hdec _ hz]
  have hcomb : (P.b₀ - P.a₀) - (a * y + b * z) * s =
      a * ((P.b₀ - P.a₀) - y * s) + b * ((P.b₀ - P.a₀) - z * s) := by
    have : (P.b₀ - P.a₀) = (a + b) * (P.b₀ - P.a₀) := by rw [hab]; ring
    linear_combination this
  rw [hcomb]
  have key := nsc_inv_comb _ _ a b (hNpos y hy) (hNpos z hz) ha0 hb0 hab
  have key' := mul_le_mul_of_nonneg_left key hCnn
  have e1 : a * (c0 + c1 * y + C * (1 / ((P.b₀ - P.a₀) - y * s))) +
      b * (c0 + c1 * z + C * (1 / ((P.b₀ - P.a₀) - z * s))) =
      (a + b) * c0 + c1 * (a * y + b * z) +
        C * (a / ((P.b₀ - P.a₀) - y * s) + b / ((P.b₀ - P.a₀) - z * s)) := by
    ring
  rw [e1, hab]
  linarith

lemma nsc_env_eq (P : Params) (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁)
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
        fun w hw => nsc_K_nonneg P ha ha₁ w hw, rfl⟩
    · rintro r ⟨g, hg, hgK, rfl⟩
      exact hup g hg hgK
  · obtain ⟨g, hg, hgK, hgv⟩ := hlow
    apply le_csSup
    · refine ⟨P.K p, ?_⟩
      rintro r ⟨g', -, hg', rfl⟩
      exact hg' p hp
    · exact ⟨g, hg, hgK, hgv.symm⟩

theorem nsc_lemma_1 (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀) :
    (P.ξh ≤ P.ξ → ∀ p ∈ Set.Icc (0:ℝ) 1,
      convexEnvelope (Set.Icc (0:ℝ) 1) P.K p = p * P.K 1 + (1 - p) * P.K 0) ∧
    ((P.a₁ - P.a₀) / (P.b₀ - P.a₀) ≤ P.ξ → P.ξ ≤ P.ξh → ∀ p ∈ Set.Icc (0:ℝ) 1,
      convexEnvelope (Set.Icc (0:ℝ) 1) P.K p = P.K p) ∧
    (P.ξ ≤ (P.a₁ - P.a₀) / (P.b₀ - P.a₀) → ∀ p ∈ Set.Icc (0:ℝ) 1,
      convexEnvelope (Set.Icc (0:ℝ) 1) P.K p =
        if p ≤ P.pHat then P.K p
        else (P.K 1 - P.K P.pHat) / (1 - P.pHat) * (p - P.pHat) + P.K P.pHat) := by
  have hL : 0 < P.b₀ - P.a₀ := by linarith
  have hl : 0 < P.b₁ - P.a₁ := by linarith
  have hα0 : 0 ≤ P.a₁ - P.a₀ := by linarith
  have hβ0 : 0 ≤ P.b₀ - P.b₁ := by linarith
  have hKpos := fun w hw => nsc_K_nonneg P ha ha₁ w hw
  have hDpos := nsc_D_pos P ha ha₁ hnest_a hnest_b
  -- K(0) and K(1)
  have hK0 : P.K 0 = (1 - P.ξ) ^ 2 * (P.b₁ - P.a₁) / 2 := by
    rw [nsc_Kmid P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b 0 ⟨le_refl 0, zero_le_one⟩
      (by unfold Params.τlow; simp; linarith) (by unfold Params.τup; simp; linarith)]
    unfold nsc_nM
    have : (P.b₀ - P.a₀) - 0 * ((P.a₁ - P.a₀) + (P.b₀ - P.b₁)) = P.b₀ - P.a₀ := by ring
    rw [this]
    field_simp
    ring
  have hK1 : P.K 1 = (1 - P.ξ) ^ 2 * (P.b₀ - P.a₀) / 2 := by
    have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
    by_cases c1 : P.τup 1 ≤ P.ξ
    · rw [nsc_K_high P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b 1 h1 c1]; ring
    by_cases c2 : P.τlow 1 ≤ P.ξ
    · rw [nsc_Kmid P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b 1 h1 c2 (not_le.mp c1).le]
      unfold nsc_nM
      have : (P.b₀ - P.a₀) - 1 * ((P.a₁ - P.a₀) + (P.b₀ - P.b₁)) = P.b₁ - P.a₁ := by ring
      rw [this]
      field_simp
      ring
    · rw [nsc_Klow P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b 1 h1 (not_le.mp c2).le]
      unfold nsc_nLo
      ring
  refine ⟨fun hξ p hp => ?_, fun hξl hξu p hp => ?_, fun hξ p hp => ?_⟩
  · ---------------- regime 1: full disclosure
    have hαs : P.a₁ - P.a₀ ≤ P.ξ * ((P.a₁ - P.a₀) + (P.b₀ - P.b₁)) := by
      rcases eq_or_lt_of_le (add_nonneg hα0 hβ0) with hs | hs
      · have e1 : P.a₁ - P.a₀ = 0 := by linarith
        have e2 : P.b₀ - P.b₁ = 0 := by linarith
        rw [e1, e2]; simp
      · unfold Params.ξh at hξ
        have e : P.b₀ - P.a₀ - P.b₁ + P.a₁ = (P.a₁ - P.a₀) + (P.b₀ - P.b₁) := by ring
        rw [e, div_le_iff₀ hs] at hξ; linarith
    apply nsc_env_eq P ha ha₁ p hp
    · intro g hg hgK
      have := hg.2 (show (1:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨zero_le_one, le_refl 1⟩)
        (show (0:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨le_refl 0, zero_le_one⟩)
        hp.1 (show 0 ≤ 1 - p by linarith [hp.2]) (show p + (1 - p) = 1 by ring)
      simp only [smul_eq_mul, mul_one, mul_zero, add_zero] at this
      have h1 := hgK 1 ⟨zero_le_one, le_refl 1⟩
      have h0 := hgK 0 ⟨le_refl 0, zero_le_one⟩
      have : p * g 1 ≤ p * P.K 1 := mul_le_mul_of_nonneg_left h1 hp.1
      have : (1 - p) * g 0 ≤ (1 - p) * P.K 0 := mul_le_mul_of_nonneg_left h0 (by linarith [hp.2])
      linarith
    · refine ⟨fun x => P.K 0 + (P.K 1 - P.K 0) * x, nsc_affine_convex _ _, fun w hw => ?_,
        by ring⟩
      show P.K 0 + (P.K 1 - P.K 0) * w ≤ P.K w
      have hw0 := hw.1; have hw1 := hw.2
      rw [hK0, hK1]
      have e : (1 - P.ξ) ^ 2 * (P.b₁ - P.a₁) / 2 +
          ((1 - P.ξ) ^ 2 * (P.b₀ - P.a₀) / 2 - (1 - P.ξ) ^ 2 * (P.b₁ - P.a₁) / 2) * w =
          w * ((1 - P.ξ) ^ 2 * (P.b₀ - P.a₀) / 2) + (1 - w) * ((1 - P.ξ) ^ 2 * (P.b₁ - P.a₁) / 2) := by
        ring
      rw [e]
      by_cases c1 : P.τup w ≤ P.ξ
      · rw [nsc_K_high P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b w hw c1]
        have hwp : 0 < w := by
          rcases eq_or_lt_of_le hw0 with h | h
          · exfalso; rw [← h] at c1; unfold Params.τup at c1; simp at c1; linarith
          · exact h
        have := nsc_d2 P.a₀ P.b₀ P.a₁ P.b₁ P.ξ w hwp.ne'
        unfold nsc_nHi at this
        have : 0 ≤ (1 - w) * (1 - P.ξ) ^ 2 * ((P.b₀ - P.a₀) + w * ((P.a₁ - P.a₀) + (P.b₀ - P.b₁))) /
            (2 * w) := by
          apply div_nonneg _ (by linarith)
          apply mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _))
          nlinarith
        linarith
      · have c2 : P.τlow w ≤ P.ξ := by
          unfold Params.τlow
          rw [div_le_iff₀ hL]
          nlinarith
        rw [nsc_Kmid P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b w hw c2 (not_le.mp c1).le]
        have hD := hDpos w hw
        have := nsc_d1 P.a₀ P.b₀ P.a₁ P.b₁ P.ξ w hL.ne' hD.ne'
        have : 0 ≤ w * (1 - w) * (P.ξ * ((P.a₁ - P.a₀) + (P.b₀ - P.b₁)) - (P.a₁ - P.a₀)) *
            ((P.a₁ - P.a₀) + 2 * (P.b₀ - P.b₁) - P.ξ * ((P.a₁ - P.a₀) + (P.b₀ - P.b₁))) /
            (2 * ((P.b₀ - P.a₀) - w * ((P.a₁ - P.a₀) + (P.b₀ - P.b₁)))) := by
          apply div_nonneg _ (by linarith)
          apply mul_nonneg (mul_nonneg (mul_nonneg hw0 (by linarith)) (by linarith))
          nlinarith
        linarith
  · ---------------- regime 2: no disclosure
    have hs : 0 < (P.a₁ - P.a₀) + (P.b₀ - P.b₁) := by
      rcases eq_or_lt_of_le (add_nonneg hα0 hβ0) with hs | hs
      · exfalso
        unfold Params.ξh at hξu
        have e : P.b₀ - P.a₀ - P.b₁ + P.a₁ = 0 := by linarith
        rw [e, div_zero] at hξu; linarith
      · exact hs
    have hξs : P.ξ * ((P.a₁ - P.a₀) + (P.b₀ - P.b₁)) ≤ P.a₁ - P.a₀ := by
      unfold Params.ξh at hξu
      have e : P.b₀ - P.a₀ - P.b₁ + P.a₁ = (P.a₁ - P.a₀) + (P.b₀ - P.b₁) := by ring
      rw [e, le_div_iff₀ hs] at hξu; linarith
    have hαL : P.a₁ - P.a₀ ≤ P.ξ * (P.b₀ - P.a₀) := by rwa [div_le_iff₀ hL] at hξl
    have hmid : ∀ w ∈ Set.Icc (0:ℝ) 1, P.K w = nsc_nM P.a₀ P.b₀ P.a₁ P.b₁ P.ξ w := by
      intro w hw
      apply nsc_Kmid P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b w hw
      · unfold Params.τlow; rw [div_le_iff₀ hL]; nlinarith [hw.2]
      · unfold Params.τup
        have : w * (P.b₀ - P.b₁) / (P.b₀ - P.a₀) ≤ 1 - P.ξ := by
          rw [div_le_iff₀ hL]; nlinarith [hw.2, hw.1]
        linarith
    apply nsc_env_eq P ha ha₁ p hp
    · intro g _ hgK; exact hgK p hp
    · refine ⟨fun x => nsc_nM P.a₀ P.b₀ P.a₁ P.b₁ P.ξ x,
        nsc_nM_convex P ha ha₁ hnest_a hnest_b hξ1 hs hξs,
        fun w hw => le_of_eq (hmid w hw).symm, (hmid p hp).symm⟩
  · ---------------- regime 3: partial disclosure
    have hreg := fun w hw => nsc_regimes P ha ha₁ hξ0 hξ1 hnest_a hnest_b hξ w hw
    have hα := (hreg p hp).1
    have hreg1 := fun w hw => (hreg w hw).2.1
    have hreg2 := fun w hw => (hreg w hw).2.2
    have hξL : P.ξ * (P.b₀ - P.a₀) ≤ P.a₁ - P.a₀ := by rwa [le_div_iff₀ hL] at hξ
    have hs : 0 < (P.a₁ - P.a₀) + (P.b₀ - P.b₁) := by linarith
    have hξs : P.ξ * ((P.a₁ - P.a₀) + (P.b₀ - P.b₁)) ≤ P.a₁ - P.a₀ := by nlinarith
    have hpH : P.pHat = P.ξ * (P.b₀ - P.a₀) / (P.a₁ - P.a₀) := rfl
    have hpHpos : 0 < P.pHat := by rw [hpH]; positivity
    have hpH1 : P.pHat ≤ 1 := by rw [hpH, div_le_one hα]; exact hξL
    have hξe : P.ξ = P.pHat * (P.a₁ - P.a₀) / (P.b₀ - P.a₀) := by
      rw [hpH]; field_simp
    have hKw : ∀ w ∈ Set.Icc (0:ℝ) 1, P.K w =
        if w ≤ P.pHat then nsc_nM P.a₀ P.b₀ P.a₁ P.b₁ P.ξ w
        else nsc_nLo P.a₀ P.b₀ P.a₁ P.b₁ P.ξ w := by
      intro w hw
      split_ifs with h
      · exact nsc_Kmid P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b w hw (hreg1 w hw h).1
          (hreg1 w hw h).2
      · exact nsc_Klow P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b w hw
          (hreg2 w hw (not_le.mp h).le)
    have hnMconv := nsc_nM_convex P ha ha₁ hnest_a hnest_b hξ1 hs hξs
    split_ifs with hpp
    · -- p ≤ p̂ : the convex minorant is the middle-regime closed form
      apply nsc_env_eq P ha ha₁ p hp
      · intro g _ hgK; exact hgK p hp
      · refine ⟨fun x => nsc_nM P.a₀ P.b₀ P.a₁ P.b₁ P.ξ x, hnMconv, fun w hw => ?_, ?_⟩
        · show nsc_nM P.a₀ P.b₀ P.a₁ P.b₁ P.ξ w ≤ P.K w
          rw [hKw w hw]
          split_ifs with h
          · exact le_refl _
          · have hwp : 0 < w := lt_trans hpHpos (not_le.mp h)
            have hD := hDpos w hw
            have hd3 := nsc_d3 P.a₀ P.b₀ P.a₁ P.b₁ P.ξ w hL.ne' hwp.ne' hD.ne'
            have hw' : P.ξ * (P.b₀ - P.a₀) ≤ (P.a₁ - P.a₀) * w := by
              have := (not_le.mp h).le
              rw [hpH, div_le_iff₀ hα] at this; linarith
            have : 0 ≤ (1 - w) * ((P.a₁ - P.a₀) * w - P.ξ * (P.b₀ - P.a₀)) *
                (2 * (P.b₀ - P.a₀) - (P.a₁ - P.a₀) * w - P.ξ * (P.b₀ - P.a₀)) /
                (2 * w * ((P.b₀ - P.a₀) - w * ((P.a₁ - P.a₀) + (P.b₀ - P.b₁)))) := by
              apply div_nonneg _ (by positivity)
              apply mul_nonneg (mul_nonneg (by linarith [hw.2]) (by linarith))
              nlinarith [hw.2]
            linarith
        · show nsc_nM P.a₀ P.b₀ P.a₁ P.b₁ P.ξ p = P.K p
          rw [hKw p hp, if_pos hpp]
    · -- p > p̂ : the chord from (p̂, K p̂) to (1, K 1)
      have hlt : P.pHat < p := not_le.mp hpp
      have hpH1' : P.pHat < 1 := lt_of_lt_of_le hlt hp.2
      have h1ne : 1 - P.pHat ≠ 0 := by linarith
      have hpHI : P.pHat ∈ Set.Icc (0:ℝ) 1 := ⟨hpHpos.le, hpH1⟩
      apply nsc_env_eq P ha ha₁ p hp
      · intro g hg hgK
        have hc := hg.2 hpHI (show (1:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨zero_le_one, le_refl 1⟩)
          (show 0 ≤ (1 - p) / (1 - P.pHat) from div_nonneg (by linarith [hp.2]) (by linarith))
          (show 0 ≤ (p - P.pHat) / (1 - P.pHat) from div_nonneg (by linarith) (by linarith))
          (show (1 - p) / (1 - P.pHat) + (p - P.pHat) / (1 - P.pHat) = 1 by field_simp; ring)
        simp only [smul_eq_mul] at hc
        have hpt : (1 - p) / (1 - P.pHat) * P.pHat + (p - P.pHat) / (1 - P.pHat) * 1 = p := by
          field_simp; ring
        rw [hpt] at hc
        have h1 := hgK 1 ⟨zero_le_one, le_refl 1⟩
        have h0 := hgK P.pHat hpHI
        have : (1 - p) / (1 - P.pHat) * g P.pHat ≤ (1 - p) / (1 - P.pHat) * P.K P.pHat :=
          mul_le_mul_of_nonneg_left h0 (div_nonneg (by linarith [hp.2]) (by linarith))
        have : (p - P.pHat) / (1 - P.pHat) * g 1 ≤ (p - P.pHat) / (1 - P.pHat) * P.K 1 :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg (by linarith) (by linarith))
        have e : (P.K 1 - P.K P.pHat) / (1 - P.pHat) * (p - P.pHat) + P.K P.pHat =
            (1 - p) / (1 - P.pHat) * P.K P.pHat + (p - P.pHat) / (1 - P.pHat) * P.K 1 := by
          field_simp; ring
        rw [e]; linarith
      · refine ⟨fun x => (P.K 1 - P.K P.pHat) / (1 - P.pHat) * (x - P.pHat) + P.K P.pHat,
          ?_, fun w hw => ?_, rfl⟩
        · have : (fun x => (P.K 1 - P.K P.pHat) / (1 - P.pHat) * (x - P.pHat) + P.K P.pHat) =
              fun x => (P.K P.pHat - (P.K 1 - P.K P.pHat) / (1 - P.pHat) * P.pHat) +
                (P.K 1 - P.K P.pHat) / (1 - P.pHat) * x := by
            funext x; ring
          rw [this]; exact nsc_affine_convex _ _
        · show (P.K 1 - P.K P.pHat) / (1 - P.pHat) * (w - P.pHat) + P.K P.pHat ≤ P.K w
          have hKp : P.K P.pHat = nsc_nM P.a₀ P.b₀ P.a₁ P.b₁ P.ξ P.pHat := by
            rw [hKw _ hpHI, if_pos (le_refl _)]
          have hDh := hDpos P.pHat hpHI
          rw [hKw w hw, hK1, hKp]
          split_ifs with h
          · have hD := hDpos w hw
            rw [hξe]
            have hd5 := nsc_d5 P.a₀ P.b₀ P.a₁ P.b₁ P.pHat w hL.ne' h1ne hDh.ne' hD.ne'
            rw [← hξe] at hd5 ⊢
            have : 0 ≤ (1 - w) * ((P.a₁ - P.a₀) * (w - P.pHat)) *
                (P.ξ * ((P.a₁ - P.a₀) + (P.b₀ - P.b₁)) - (P.a₁ - P.a₀) - 2 * (P.b₀ - P.b₁)) /
                (2 * ((P.b₀ - P.a₀) - w * ((P.a₁ - P.a₀) + (P.b₀ - P.b₁)))) := by
              apply div_nonneg _ (by linarith)
              apply mul_nonneg_of_nonpos_of_nonpos
              · apply mul_nonpos_of_nonneg_of_nonpos (by linarith [hw.2])
                apply mul_nonpos_of_nonneg_of_nonpos hα.le (by linarith)
              · linarith
            linarith
          · have hwp : 0 < w := lt_trans hpHpos (not_le.mp h)
            rw [hξe]
            have hd4 := nsc_d4 P.a₀ P.b₀ P.a₁ P.b₁ P.pHat w hL.ne' hwp.ne' h1ne hDh.ne'
            rw [← hξe] at hd4 ⊢
            have : 0 ≤ (1 - w) * (2 - P.ξ) * ((P.a₁ - P.a₀) * (w - P.pHat)) / (2 * w) := by
              apply div_nonneg _ (by linarith)
              apply mul_nonneg (mul_nonneg (by linarith [hw.2]) (by linarith))
              exact mul_nonneg hα.le (by linarith [(not_le.mp h).le])
            linarith

theorem solution (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀) :
    (P.ξh ≤ P.ξ → ∀ p ∈ Set.Icc (0:ℝ) 1,
      convexEnvelope (Set.Icc (0:ℝ) 1) P.K p = p * P.K 1 + (1 - p) * P.K 0) ∧
    ((P.a₁ - P.a₀) / (P.b₀ - P.a₀) ≤ P.ξ → P.ξ ≤ P.ξh → ∀ p ∈ Set.Icc (0:ℝ) 1,
      convexEnvelope (Set.Icc (0:ℝ) 1) P.K p = P.K p) ∧
    (P.ξ ≤ (P.a₁ - P.a₀) / (P.b₀ - P.a₀) → ∀ p ∈ Set.Icc (0:ℝ) 1,
      convexEnvelope (Set.Icc (0:ℝ) 1) P.K p =
        if p ≤ P.pHat then P.K p
        else (P.K 1 - P.K P.pHat) / (1 - P.pHat) * (p - P.pHat) + P.K P.pHat) :=
  nsc_lemma_1 P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b
