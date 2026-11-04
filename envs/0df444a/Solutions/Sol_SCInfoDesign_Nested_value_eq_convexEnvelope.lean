-- Prove2me | solution 1 for SCInfoDesign.Nested.value_eq_convexEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T19:06:35.064895+00:00
-- url     : https://prove2.me/submissions/d42a8fc9-b514-4476-925d-4ccb8aec3fd9

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

theorem solution (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0:ℝ) 1) :
    IsGLB {c : ℝ | ∃ (n : ℕ) (π : Fin 2 → Fin n → ℝ) (Qs : ℝ → ℝ),
        IsPolicy π ∧ P.IsBestResponseProfile Qs ∧ c = P.expectedCost p₀ π Qs}
      (convexEnvelope (Set.Icc (0:ℝ) 1) P.K p₀) :=
  nsc_value P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b p₀ hp₀
