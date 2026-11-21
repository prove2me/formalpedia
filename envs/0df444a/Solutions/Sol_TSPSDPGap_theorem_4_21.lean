-- Prove2me | solution 1 for TSPSDPGap.theorem_4_21
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:53:56.32672+00:00
-- url     : https://prove2.me/submissions/3660e4bf-69e5-4fad-95e8-74bb8d5b5e1d

import Mathlib
import Definitions.Def_TSPSDPGap_sdp1Objective
import Definitions.Def_TSPSDPGap_simplicialCost
import Definitions.Def_TSPSDPGap_Ymat

open scoped Kronecker

namespace TSPSDPGap

namespace Aux_T421

open Finset

lemma reflect_sum (g : ℕ) (θ : ℝ) :
    ∑ j ∈ range g, Real.cos (((g:ℝ) - j) * θ) = ∑ d ∈ Finset.Ico 1 (g + 1), Real.cos ((d:ℝ) * θ) := by
  rw [Finset.sum_Ico_eq_sum_range, show g + 1 - 1 = g by omega]
  rw [← Finset.sum_range_reflect (fun k => Real.cos (((1 + k : ℕ) : ℝ) * θ)) g]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' := Finset.mem_range.mp hj
  have e : ((1 + (g - 1 - j) : ℕ) : ℝ) = (g:ℝ) - j := by
    rw [show 1 + (g - 1 - j) = g - j by omega, Nat.cast_sub hj'.le]
  rw [e]

lemma fejer (g : ℕ) (θ : ℝ) :
    (g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (j * θ)
      = (∑ j ∈ range g, Real.cos (j * θ)) ^ 2 + (∑ j ∈ range g, Real.sin (j * θ)) ^ 2 := by
  induction g with
  | zero => simp
  | succ g ih =>
    rcases Nat.eq_zero_or_pos g with h0 | hpos
    · subst h0
      simp
    have h1 : 1 ≤ g := hpos
    have hsplit : ∑ j ∈ Finset.Ico 1 (g + 1), (((g + 1 : ℕ) : ℝ) - j) * Real.cos (j * θ)
        = ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (j * θ)
          + ∑ j ∈ Finset.Ico 1 (g + 1), Real.cos (j * θ) := by
      rw [Finset.sum_Ico_succ_top h1, Finset.sum_Ico_succ_top h1]
      have e : ∑ j ∈ Finset.Ico 1 g, (((g + 1 : ℕ) : ℝ) - j) * Real.cos (j * θ)
          = ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (j * θ)
            + ∑ j ∈ Finset.Ico 1 g, Real.cos (j * θ) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        push_cast
        ring
      rw [e]
      push_cast
      ring
    have hcross : ∑ j ∈ range g, Real.cos (((g:ℝ) - j) * θ)
        = (∑ j ∈ range g, Real.cos (j * θ)) * Real.cos (g * θ)
          + (∑ j ∈ range g, Real.sin (j * θ)) * Real.sin (g * θ) := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [show ((g:ℝ) - j) * θ = g * θ - j * θ by ring, Real.cos_sub]
      ring
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hsplit, ← reflect_sum, hcross]
    push_cast
    linear_combination ih - Real.sin_sq_add_cos_sq ((g:ℝ) * θ)

lemma fejer_le (g : ℕ) (θ : ℝ) :
    (∑ j ∈ range g, Real.cos (j * θ)) ^ 2 + (∑ j ∈ range g, Real.sin (j * θ)) ^ 2
      ≤ (g:ℝ) ^ 2 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := range g) (f := fun j : ℕ => Real.cos (j * θ))
  have h2 := sq_sum_le_card_mul_sum_sq (s := range g) (f := fun j : ℕ => Real.sin (j * θ))
  have h3 : ∑ j ∈ range g, Real.cos (j * θ) ^ 2 + ∑ j ∈ range g, Real.sin (j * θ) ^ 2 = g := by
    rw [← Finset.sum_add_distrib]
    have : ∀ j ∈ range g, Real.cos (j * θ) ^ 2 + Real.sin (j * θ) ^ 2 = 1 := fun j _ => by
      rw [add_comm]; exact Real.sin_sq_add_cos_sq _
    rw [Finset.sum_congr rfl this]
    simp
  simp only [Finset.card_range] at h1 h2
  have h4 : (g:ℝ) * (∑ j ∈ range g, Real.cos (j * θ) ^ 2 + ∑ j ∈ range g, Real.sin (j * θ) ^ 2)
      = (g:ℝ) * g := by rw [h3]
  nlinarith [h1, h2, h4]

lemma mod2 (a n : ℕ) (h : a < 2 * n) : a % n = if a < n then a else a - n := by
  split_ifs with h1
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

lemma circ_row (n i : ℕ) (hi1 : 1 ≤ i) (hin : i < n) (s : Fin n) :
    ∑ t, circBasis n i s t = 2 := by
  have hn : 0 < n := by omega
  unfold circBasis
  simp only [Matrix.of_apply]
  rw [Finset.sum_add_distrib, Nat.mod_eq_of_lt hin]
  have h1 : ∀ t : Fin n, (((t : ℕ) + n - s) % n = i ↔ t = ⟨((s : ℕ) + i) % n, Nat.mod_lt _ hn⟩) := by
    intro t
    have := s.isLt
    have := t.isLt
    rw [Fin.ext_iff]
    simp only
    rw [mod2 _ _ (by omega), mod2 ((s : ℕ) + i) n (by omega)]
    split_ifs <;> omega
  have h2 : ∀ t : Fin n, (((s : ℕ) + n - t) % n = i ↔ t = ⟨((s : ℕ) + n - i) % n, Nat.mod_lt _ hn⟩) := by
    intro t
    have := s.isLt
    have := t.isLt
    rw [Fin.ext_iff]
    simp only
    rw [mod2 _ _ (by omega), mod2 ((s : ℕ) + n - i) n (by omega)]
    split_ifs <;> omega
  simp only [h1, h2]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte]
  norm_num

lemma circ_le2 (m i : ℕ) (s t : Fin m) : circBasis m i s t ≤ 2 := by
  unfold circBasis
  simp only [Matrix.of_apply]
  split_ifs <;> norm_num

lemma circ_nonneg' (m i : ℕ) (s t : Fin m) : 0 ≤ circBasis m i s t := by
  unfold circBasis
  simp only [Matrix.of_apply]
  split_ifs <;> norm_num

lemma circ_disj (n k : ℕ) (hn : 4 ≤ n) (hk2 : 2 ≤ k) (hkn : k ≤ n / 2) (i j : Fin n) :
    circBasis n 1 i j * circBasis n k j i = 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold circBasis
  simp only [Matrix.of_apply]
  rw [Nat.mod_eq_of_lt (show 1 < n by omega), Nat.mod_eq_of_lt (show k < n by omega),
    mod2 ((j : ℕ) + n - i) n (by omega), mod2 ((i : ℕ) + n - j) n (by omega)]
  split_ifs <;> (try norm_num) <;> omega

lemma gap (g : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    (g:ℝ) ^ 2 - ((∑ j ∈ range g, Real.cos (j * θ)) ^ 2 + (∑ j ∈ range g, Real.sin (j * θ)) ^ 2)
      ≤ (g:ℝ) ^ 4 * θ ^ 2 := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∑ j ∈ range g, Real.cos (j * θ) := ⟨_, rfl⟩
  rw [← hC]
  have hC1 : (g:ℝ) - C = ∑ j ∈ range g, (1 - Real.cos (j * θ)) := by
    rw [Finset.sum_sub_distrib, hC]; simp
  have hC2 : ∑ j ∈ range g, (1 - Real.cos (j * θ)) ≤ ∑ _j ∈ range g, ((g:ℝ) * θ) ^ 2 / 2 := by
    apply Finset.sum_le_sum
    intro j hj
    have hj' : (j:ℝ) ≤ g := by exact_mod_cast (Finset.mem_range.mp hj).le
    have h1 := Real.one_sub_sq_div_two_le_cos (x := (j:ℝ) * θ)
    have h2 : ((j:ℝ) * θ) ^ 2 ≤ ((g:ℝ) * θ) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg j) hθ)
        (mul_le_mul_of_nonneg_right hj' hθ) 2
    linarith
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hC2
  have hCle : C ≤ g := by
    rw [hC]
    calc ∑ j ∈ range g, Real.cos (j * θ) ≤ ∑ _j ∈ range g, (1:ℝ) :=
          Finset.sum_le_sum (fun j _ => Real.cos_le_one _)
      _ = g := by simp
  have hCge : -(g:ℝ) ≤ C := by
    rw [hC]
    calc -(g:ℝ) = ∑ _j ∈ range g, (-1:ℝ) := by simp
      _ ≤ ∑ j ∈ range g, Real.cos (j * θ) :=
          Finset.sum_le_sum (fun j _ => Real.neg_one_le_cos _)
  have hprod : ((g:ℝ) - C) * ((g:ℝ) + C) ≤ ((g:ℝ) * (((g:ℝ) * θ) ^ 2 / 2)) * (2 * g) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
  nlinarith [hprod, sq_nonneg (∑ j ∈ range g, Real.sin (j * θ))]

lemma b1_bound (g n m : ℕ) (hg2 : 2 ≤ g) (hlt : g < n) (hm : m = n / 2) (hm2 : 2 * m = n)
    (hmge : 2 ≤ m) :
    0 ≤ coeffB g n 1 ∧ coeffB g n 1 ≤ 8 * Real.pi ^ 2 * (g:ℝ) ^ 3 / (n:ℝ) ^ 3 := by
  have h1m : 1 < n / 2 := by omega
  have hg0 : (0:ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hng : (0:ℝ) < (n:ℝ) - g := by
    have : (g:ℝ) < n := by exact_mod_cast hlt
    linarith
  have hg1 : (1:ℝ) ≤ (g:ℝ) - 1 := by
    have : (2:ℝ) ≤ g := by exact_mod_cast hg2
    linarith
  have hmR : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnR : (n:ℝ) = 2 * m := by exact_mod_cast hm2.symm
  have hn0 : (0:ℝ) < n := by rw [hnR]; linarith
  have hgg : (g:ℝ) / g = 1 := div_self hg0.ne'
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = Real.pi / m := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ∑ j ∈ Finset.Ico 1 g, ((g:ℝ) - j)
      * Real.cos (Real.pi * ((1:ℕ):ℝ) * (j:ℝ) / ((n / 2 : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hPθ : P = ∑ j ∈ Finset.Ico 1 g, ((g:ℝ) - j) * Real.cos (j * θ) := by
    rw [hP]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← hm, hθ, Nat.cast_one]
    congr 2
    ring
  have hX := fejer g θ
  rw [← hPθ] at hX
  have hgap := gap g θ hθ0
  have hle := fejer_le g θ
  rw [← hX] at hgap hle
  have hcancel : ∀ X : ℝ, ((n:ℝ) - g) * (1 / ((n:ℝ) - g) * X) = X := by
    intro X
    rw [← mul_assoc, mul_one_div_cancel hng.ne', one_mul]
  have hcB : coeffB g n 1 = (2 * (g:ℝ) - (2 + 4 / (g:ℝ) * P)) / ((n:ℝ) * ((g:ℝ) - 1)) := by
    unfold coeffB coeffA
    rw [if_pos h1m, if_pos h1m, ← hP, hcancel]
  have hnum : 2 * (g:ℝ) - (2 + 4 / (g:ℝ) * P) = 2 / (g:ℝ) * ((g:ℝ) ^ 2 - ((g:ℝ) + 2 * P)) := by
    have e : 2 / (g:ℝ) * ((g:ℝ) ^ 2 - ((g:ℝ) + 2 * P))
        = 2 * g * ((g:ℝ) / g) - (2 * ((g:ℝ) / g) + 4 / (g:ℝ) * P) := by ring
    rw [e, hgg, mul_one, mul_one]
  have hnum0 : 0 ≤ 2 * (g:ℝ) - (2 + 4 / (g:ℝ) * P) := by
    rw [hnum]
    exact mul_nonneg (by positivity) (by linarith)
  have hnum1 : 2 * (g:ℝ) - (2 + 4 / (g:ℝ) * P) ≤ 2 * (g:ℝ) ^ 3 * θ ^ 2 := by
    rw [hnum]
    calc 2 / (g:ℝ) * ((g:ℝ) ^ 2 - ((g:ℝ) + 2 * P)) ≤ 2 / (g:ℝ) * ((g:ℝ) ^ 4 * θ ^ 2) :=
          mul_le_mul_of_nonneg_left hgap (by positivity)
      _ = 2 * (g:ℝ) ^ 3 * θ ^ 2 * ((g:ℝ) / g) := by ring
      _ = 2 * (g:ℝ) ^ 3 * θ ^ 2 := by rw [hgg, mul_one]
  have hden : 0 < (n:ℝ) * ((g:ℝ) - 1) := mul_pos hn0 (by linarith)
  rw [hcB]
  refine ⟨div_nonneg hnum0 hden.le, ?_⟩
  calc (2 * (g:ℝ) - (2 + 4 / (g:ℝ) * P)) / ((n:ℝ) * ((g:ℝ) - 1))
      ≤ (2 * (g:ℝ) - (2 + 4 / (g:ℝ) * P)) / n :=
        div_le_div_of_nonneg_left hnum0 hn0 (by nlinarith)
    _ ≤ (2 * (g:ℝ) ^ 3 * θ ^ 2) / n := div_le_div_of_nonneg_right hnum1 hn0.le
    _ = 8 * Real.pi ^ 2 * (g:ℝ) ^ 3 / (n:ℝ) ^ 3 := by
        rw [hθ, hnR]
        first | (field_simp; ring) | field_simp

lemma sum4 {α β : Type*} [Fintype α] [Fintype β] (F : α → α → ℝ) (G : β → β → ℝ) :
    ∑ p, ∑ q, ∑ i, ∑ j, F p q * G i j = (∑ p, ∑ q, F p q) * (∑ i, ∑ j, G i j) := by
  symm
  rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]

end Aux_T421

end TSPSDPGap

open TSPSDPGap TSPSDPGap.Aux_T421 in
theorem solution (g : ℕ) (hg : Even g) (hg2 : 2 ≤ g) :
    ∃ c : ℝ, ∀ n : ℕ, g ∣ n → g < n →
      sdp1Objective n (simplicialCost g n) (Ymat g n) ≤ c / n := by
  refine ⟨8 * Real.pi ^ 2 * (g:ℝ) ^ 3, ?_⟩
  intro n hgn hlt
  obtain ⟨q, hq⟩ := hgn
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with h | h
    · interval_cases q <;> omega
    · exact h
  have hn4 : 4 ≤ n := by rw [hq]; nlinarith
  have hneven : Even n := by rw [hq]; exact hg.mul_right q
  obtain ⟨m, hm⟩ : ∃ m, m = n / 2 := ⟨_, rfl⟩
  have hm2 : 2 * m = n := by rw [hm]; exact Nat.two_mul_div_two_of_even hneven
  have hmge : 2 ≤ m := by omega
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hb0, hb1⟩ := b1_bound g n m hg2 hlt hm hm2 hmge
  -- pointwise description of the summand
  have hpt : ∀ p q : Fin n, ∀ i j : Fin n,
      simplicialCost g n p q * circBasis n 1 i j * Ymat g n (q, j) (p, i)
        = simplicialCost g n p q * (1 / (2 * (n:ℝ)) * (circBasis n 1 i j * Bmat g n j i)) := by
    intro p q i j
    unfold simplicialCost Ymat
    simp only [Matrix.of_apply]
    by_cases h : (p : ℕ) / (n / g) = (q : ℕ) / (n / g)
    · simp only [h, ↓reduceIte, zero_mul]
    · have hqp : ¬ q = p := fun e => h (by rw [e])
      have h' : ¬ (q : ℕ) / (n / g) = (p : ℕ) / (n / g) := fun e => h e.symm
      simp only [h, hqp, h', ↓reduceIte]
      ring
  have hobj : sdp1Objective n (simplicialCost g n) (Ymat g n)
      = (1 / 2) * ((∑ p : Fin n, ∑ q : Fin n, simplicialCost g n p q) *
        (∑ i : Fin n, ∑ j : Fin n, 1 / (2 * (n:ℝ)) * (circBasis n 1 i j * Bmat g n j i))) := by
    unfold sdp1Objective
    congr 1
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.kronecker_apply, Matrix.kroneckerMap_apply]
    rw [Finset.sum_congr rfl (fun p _ => Finset.sum_comm)]
    simp only [hpt]
    exact sum4 (fun p q => simplicialCost g n p q)
      (fun i j => 1 / (2 * (n:ℝ)) * (circBasis n 1 i j * Bmat g n j i))
  -- the circulant contribution
  have hK : ∀ i j : Fin n, circBasis n 1 i j * Bmat g n j i
      = coeffB g n 1 * (circBasis n 1 i j * circBasis n 1 j i) := by
    intro i j
    unfold Bmat
    rw [Matrix.sum_apply, Finset.mul_sum, Finset.sum_eq_single 1]
    · rw [Matrix.smul_apply, smul_eq_mul]; ring
    · intro k hk hk1
      have hk' := Finset.mem_Icc.mp hk
      rw [Matrix.smul_apply, smul_eq_mul,
        show circBasis n 1 i j * (coeffB g n k * circBasis n k j i)
          = coeffB g n k * (circBasis n 1 i j * circBasis n k j i) by ring,
        circ_disj n k hn4 (by omega) hk'.2 i j, mul_zero]
    · intro h1
      exfalso
      exact h1 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hrow : ∀ i : Fin n, ∑ j : Fin n, circBasis n 1 i j = 2 :=
    fun i => circ_row n 1 le_rfl (by omega) i
  have hKsum : ∑ i : Fin n, ∑ j : Fin n, 1 / (2 * (n:ℝ)) * (circBasis n 1 i j * Bmat g n j i)
      ≤ 2 * coeffB g n 1 := by
    have e1 : ∀ i j : Fin n, 1 / (2 * (n:ℝ)) * (circBasis n 1 i j * Bmat g n j i)
        ≤ 1 / (2 * (n:ℝ)) * (coeffB g n 1 * (2 * circBasis n 1 i j)) := by
      intro i j
      rw [hK]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine mul_le_mul_of_nonneg_left ?_ hb0
      have := circ_le2 n 1 j i
      have := circ_nonneg' n 1 i j
      nlinarith
    calc ∑ i : Fin n, ∑ j : Fin n, 1 / (2 * (n:ℝ)) * (circBasis n 1 i j * Bmat g n j i)
        ≤ ∑ i : Fin n, ∑ j : Fin n, 1 / (2 * (n:ℝ)) * (coeffB g n 1 * (2 * circBasis n 1 i j)) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => e1 i j))
      _ = ∑ i : Fin n, 1 / (2 * (n:ℝ)) * (coeffB g n 1 * (2 * ∑ j : Fin n, circBasis n 1 i j)) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      _ = ∑ _i : Fin n, 1 / (2 * (n:ℝ)) * (coeffB g n 1 * 4) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hrow i]; ring
      _ = 2 * coeffB g n 1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          first | (field_simp; ring) | field_simp
  have hKnn : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, 1 / (2 * (n:ℝ)) * (circBasis n 1 i j * Bmat g n j i) := by
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro j _
    rw [hK]
    exact mul_nonneg (by positivity)
      (mul_nonneg hb0 (mul_nonneg (circ_nonneg' n 1 i j) (circ_nonneg' n 1 j i)))
  have hDle : ∑ p : Fin n, ∑ q : Fin n, simplicialCost g n p q ≤ (n:ℝ) ^ 2 := by
    calc ∑ p : Fin n, ∑ q : Fin n, simplicialCost g n p q ≤ ∑ _p : Fin n, ∑ _q : Fin n, (1:ℝ) := by
          apply Finset.sum_le_sum; intro p _
          apply Finset.sum_le_sum; intro q _
          unfold simplicialCost
          simp only [Matrix.of_apply]
          split_ifs <;> norm_num
      _ = (n:ℝ) ^ 2 := by first | (simp; ring) | simp
  have hDnn : 0 ≤ ∑ p : Fin n, ∑ q : Fin n, simplicialCost g n p q := by
    apply Finset.sum_nonneg; intro p _
    apply Finset.sum_nonneg; intro q _
    unfold simplicialCost
    simp only [Matrix.of_apply]
    split_ifs <;> norm_num
  rw [hobj]
  calc (1 / 2) * ((∑ p : Fin n, ∑ q : Fin n, simplicialCost g n p q) *
        (∑ i : Fin n, ∑ j : Fin n, 1 / (2 * (n:ℝ)) * (circBasis n 1 i j * Bmat g n j i)))
      ≤ (1 / 2) * ((n:ℝ) ^ 2 * (2 * coeffB g n 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul hDle hKsum hKnn (by positivity)
    _ = (n:ℝ) ^ 2 * coeffB g n 1 := by ring
    _ ≤ (n:ℝ) ^ 2 * (8 * Real.pi ^ 2 * (g:ℝ) ^ 3 / (n:ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hb1 (by positivity)
    _ = 8 * Real.pi ^ 2 * (g:ℝ) ^ 3 / n := by
        first | (field_simp; ring) | field_simp
