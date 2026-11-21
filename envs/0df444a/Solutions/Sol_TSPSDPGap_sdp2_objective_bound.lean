-- Prove2me | solution 1 for TSPSDPGap.sdp2_objective_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:05:45.926585+00:00
-- url     : https://prove2.me/submissions/4742dfd1-2ed9-418c-b555-63fc691dc2b5

import Mathlib
import Definitions.Def_TSPSDPGap_sdp2Objective
import Definitions.Def_TSPSDPGap_simplicialCostExt
import Definitions.Def_TSPSDPGap_Ymat

open scoped Kronecker

namespace TSPSDPGap

namespace Aux_SDP2

open Finset

def sc (g n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun p q => if (p : ℕ) / (n / g) = (q : ℕ) / (n / g) then 0 else 1

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

/-- Bounds `0 ≤ g + 2P ≤ g²` for the Fejér-type sum appearing in `coeffA`. -/
lemma key (g n i : ℕ) :
    0 ≤ (g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (Real.pi * i * j / (n / 2 : ℕ))
    ∧ (g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (Real.pi * i * j / (n / 2 : ℕ))
      ≤ (g : ℝ) ^ 2 := by
  have e : ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (Real.pi * i * j / (n / 2 : ℕ))
      = ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (j * (Real.pi * i / (n / 2 : ℕ))) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show Real.pi * (i:ℝ) * (j:ℝ) / ((n / 2 : ℕ) : ℝ)
      = (j:ℝ) * (Real.pi * i / ((n / 2 : ℕ) : ℝ)) by ring]
  rw [e, fejer]
  exact ⟨by positivity, fejer_le g _⟩

lemma circ_nonneg (m i : ℕ) (s t : Fin m) : 0 ≤ circBasis m i s t := by
  unfold circBasis
  simp only [Matrix.of_apply]
  split_ifs <;> norm_num


lemma t421b (g : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (n : ℕ) (hgn : g ∣ n) (hlt : g < n) :
    (1 / 2 : ℝ) * ∑ p : Fin n, ∑ i : Fin n, ∑ q : Fin n, ∑ j : Fin n,
      sc g n p q * circBasis n 1 i j * Ymat g n (q, j) (p, i) ≤ 8 * Real.pi ^ 2 * (g:ℝ) ^ 3 / n := by
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
      sc g n p q * circBasis n 1 i j * Ymat g n (q, j) (p, i)
        = sc g n p q * (1 / (2 * (n:ℝ)) * (circBasis n 1 i j * Bmat g n j i)) := by
    intro p q i j
    unfold sc Ymat
    simp only [Matrix.of_apply]
    by_cases h : (p : ℕ) / (n / g) = (q : ℕ) / (n / g)
    · simp only [h, ↓reduceIte, zero_mul]
    · have hqp : ¬ q = p := fun e => h (by rw [e])
      have h' : ¬ (q : ℕ) / (n / g) = (p : ℕ) / (n / g) := fun e => h e.symm
      simp only [h, hqp, h', ↓reduceIte]
      ring
  have hobj : (1 / 2 : ℝ) * ∑ p : Fin n, ∑ i : Fin n, ∑ q : Fin n, ∑ j : Fin n,
      sc g n p q * circBasis n 1 i j * Ymat g n (q, j) (p, i)
      = (1 / 2) * ((∑ p : Fin n, ∑ q : Fin n, sc g n p q) *
        (∑ i : Fin n, ∑ j : Fin n, 1 / (2 * (n:ℝ)) * (circBasis n 1 i j * Bmat g n j i))) := by
    congr 1
    rw [Finset.sum_congr rfl (fun p _ => Finset.sum_comm)]
    simp only [hpt]
    exact sum4 (fun p q => sc g n p q)
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
  have hDle : ∑ p : Fin n, ∑ q : Fin n, sc g n p q ≤ (n:ℝ) ^ 2 := by
    calc ∑ p : Fin n, ∑ q : Fin n, sc g n p q ≤ ∑ _p : Fin n, ∑ _q : Fin n, (1:ℝ) := by
          apply Finset.sum_le_sum; intro p _
          apply Finset.sum_le_sum; intro q _
          unfold sc
          simp only [Matrix.of_apply]
          split_ifs <;> norm_num
      _ = (n:ℝ) ^ 2 := by first | (simp; ring) | simp
  have hDnn : 0 ≤ ∑ p : Fin n, ∑ q : Fin n, sc g n p q := by
    apply Finset.sum_nonneg; intro p _
    apply Finset.sum_nonneg; intro q _
    unfold sc
    simp only [Matrix.of_apply]
    split_ifs <;> norm_num
  rw [hobj]
  calc (1 / 2) * ((∑ p : Fin n, ∑ q : Fin n, sc g n p q) *
        (∑ i : Fin n, ∑ j : Fin n, 1 / (2 * (n:ℝ)) * (circBasis n 1 i j * Bmat g n j i)))
      ≤ (1 / 2) * ((n:ℝ) ^ 2 * (2 * coeffB g n 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul hDle hKsum hKnn (by positivity)
    _ = (n:ℝ) ^ 2 * coeffB g n 1 := by ring
    _ ≤ (n:ℝ) ^ 2 * (8 * Real.pi ^ 2 * (g:ℝ) ^ 3 / (n:ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hb1 (by positivity)
    _ = 8 * Real.pi ^ 2 * (g:ℝ) ^ 3 / n := by
        first | (field_simp; ring) | field_simp

lemma c412 (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    (∀ i ∈ Finset.Icc 1 (n / 2), 0 ≤ coeffA g n i) ∧
    (∀ i ∈ Finset.Icc 1 (n / 2), 0 ≤ coeffB g n i) ∧
    ∀ a b, 0 ≤ Ymat g n a b := by
  have hg0 : (0:ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hg1 : (0:ℝ) < (g:ℝ) - 1 := by
    have : (2:ℝ) ≤ g := by exact_mod_cast hg2
    linarith
  have hng : (0:ℝ) < (n:ℝ) - g := by
    have : (g:ℝ) < n := by exact_mod_cast hlt
    linarith
  have hn0 : (0:ℝ) < n := by
    have : (g:ℝ) < n := by exact_mod_cast hlt
    linarith
  have hgg : (g:ℝ) / g = 1 := div_self hg0.ne'
  have hA : ∀ i, 0 ≤ coeffA g n i := by
    intro i
    obtain ⟨k0, k1⟩ := key g n i
    unfold coeffA
    split_ifs
    · have e : (2:ℝ) + 4 / g * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ))
          = 2 / g * ((g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ))) := by
        have e2 : 2 / (g:ℝ) * ((g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ)))
            = 2 * ((g:ℝ) / g) + 4 / g * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ)) := by ring
        rw [e2, hgg, mul_one]
      rw [e]
      exact mul_nonneg (one_div_nonneg.2 hng.le) (mul_nonneg (by positivity) k0)
    · have e : (1:ℝ) + 2 / g * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ))
          = 1 / g * ((g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ))) := by
        have e2 : 1 / (g:ℝ) * ((g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ)))
            = (g:ℝ) / g + 2 / g * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ)) := by ring
        rw [e2, hgg]
      rw [e]
      exact mul_nonneg (one_div_nonneg.2 hng.le) (mul_nonneg (by positivity) k0)
  have hB : ∀ i, 0 ≤ coeffB g n i := by
    intro i
    obtain ⟨k0, k1⟩ := key g n i
    obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
        * Real.cos (Real.pi * i * j / (n / 2 : ℕ)) := ⟨_, rfl⟩
    rw [← hP] at k0 k1
    have hden : 0 < (n:ℝ) * ((g:ℝ) - 1) := mul_pos hn0 hg1
    have hcancel : ∀ X : ℝ, ((n:ℝ) - g) * (1 / ((n:ℝ) - g) * X) = X := by
      intro X
      rw [← mul_assoc, mul_one_div_cancel hng.ne', one_mul]
    unfold coeffB coeffA
    split_ifs with h
    · rw [← hP, hcancel]
      refine div_nonneg ?_ hden.le
      have e : (2:ℝ) + 4 / g * P = 2 / g * ((g : ℝ) + 2 * P) := by
        have e2 : 2 / (g:ℝ) * ((g : ℝ) + 2 * P) = 2 * ((g:ℝ) / g) + 4 / g * P := by ring
        rw [e2, hgg, mul_one]
      rw [e]
      have : 2 / (g:ℝ) * ((g : ℝ) + 2 * P) ≤ 2 / g * (g:ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left k1 (by positivity)
      have e3 : 2 / (g:ℝ) * (g:ℝ) ^ 2 = 2 * g * ((g:ℝ) / g) := by ring
      rw [e3, hgg, mul_one] at this
      linarith
    · rw [← hP, hcancel]
      refine div_nonneg ?_ hden.le
      have e : (1:ℝ) + 2 / g * P = 1 / g * ((g : ℝ) + 2 * P) := by
        have e2 : 1 / (g:ℝ) * ((g : ℝ) + 2 * P) = (g:ℝ) / g + 2 / g * P := by ring
        rw [e2, hgg]
      rw [e]
      have : 1 / (g:ℝ) * ((g : ℝ) + 2 * P) ≤ 1 / g * (g:ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left k1 (by positivity)
      have e3 : 1 / (g:ℝ) * (g:ℝ) ^ 2 = g * ((g:ℝ) / g) := by ring
      rw [e3, hgg, mul_one] at this
      linarith
  refine ⟨fun i _ => hA i, fun i _ => hB i, ?_⟩
  intro a b
  have hAm : ∀ s t, 0 ≤ Amat g n s t := by
    intro s t
    unfold Amat
    rw [Matrix.sum_apply]
    exact Finset.sum_nonneg (fun i _ => by
      rw [Matrix.smul_apply, smul_eq_mul]
      exact mul_nonneg (hA i) (circ_nonneg n i s t))
  have hBm : ∀ s t, 0 ≤ Bmat g n s t := by
    intro s t
    unfold Bmat
    rw [Matrix.sum_apply]
    exact Finset.sum_nonneg (fun i _ => by
      rw [Matrix.smul_apply, smul_eq_mul]
      exact mul_nonneg (hB i) (circ_nonneg n i s t))
  unfold Ymat
  simp only [Matrix.of_apply]
  apply mul_nonneg (by positivity)
  split_ifs
  · norm_num
  · norm_num
  · exact hAm _ _
  · exact hBm _ _


lemma sa_val {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    ((p.succAbove i : Fin (n + 1)) : ℕ) = if (i : ℕ) < (p : ℕ) then (i : ℕ) else (i : ℕ) + 1 := by
  by_cases h : (i : ℕ) < (p : ℕ)
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using h)]
    simp
  · rw [if_neg h, Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]
    simp

lemma modone_fin (N : ℕ) (hN : 2 ≤ N) (a b : Fin N) :
    (((b : ℕ) + N - a) % N = 1 % N) ↔ ((b : ℕ) = a + 1 ∨ ((a : ℕ) = N - 1 ∧ (b : ℕ) = 0)) := by
  have ha := a.isLt
  have hb := b.isLt
  rw [Nat.mod_eq_of_lt (show 1 < N by omega), mod2 _ _ (by omega)]
  split_ifs <;> omega

lemma csub_le (n : ℕ) (hn : 2 ≤ n) (r : Fin (n + 1)) (i j : Fin n) :
    circBasis (n + 1) 1 (r.succAbove i) (r.succAbove j) ≤ circBasis n 1 i j := by
  have hi := i.isLt
  have hj := j.isLt
  have hr := r.isLt
  have ha : (((r.succAbove i : Fin (n + 1)) : ℕ) = i ∧ (i : ℕ) < r) ∨
      (((r.succAbove i : Fin (n + 1)) : ℕ) = i + 1 ∧ (r : ℕ) ≤ i) := by
    rw [sa_val]; split_ifs <;> omega
  have hb : (((r.succAbove j : Fin (n + 1)) : ℕ) = j ∧ (j : ℕ) < r) ∨
      (((r.succAbove j : Fin (n + 1)) : ℕ) = j + 1 ∧ (r : ℕ) ≤ j) := by
    rw [sa_val]; split_ifs <;> omega
  have hai := (r.succAbove i).isLt
  have hbj := (r.succAbove j).isLt
  unfold circBasis
  simp only [Matrix.of_apply, modone_fin (n + 1) (by omega), modone_fin n hn]
  rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hb with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    split_ifs <;> (try norm_num) <;> omega

lemma circ_symm (m i : ℕ) (s t : Fin m) : circBasis m i s t = circBasis m i t s := by
  unfold circBasis
  simp only [Matrix.of_apply]
  ring

lemma col_sum_le (n : ℕ) (r : Fin (n + 1)) (hn : 1 ≤ n) :
    ∑ i : Fin n, circBasis (n + 1) 1 (r.succAbove i) r ≤ 2 := by
  have h : ∑ a : Fin (n + 1), circBasis (n + 1) 1 a r
      = circBasis (n + 1) 1 r r + ∑ i : Fin n, circBasis (n + 1) 1 (r.succAbove i) r :=
    Fin.sum_univ_succAbove (fun a => circBasis (n + 1) 1 a r) r
  have htot : ∑ a : Fin (n + 1), circBasis (n + 1) 1 a r = 2 := by
    rw [← circ_row (n + 1) 1 le_rfl (by omega) r]
    exact Finset.sum_congr rfl (fun a _ => circ_symm _ _ _ _)
  have h0 := circ_nonneg' (n + 1) 1 r r
  linarith

lemma sc_nonneg (g n : ℕ) (p q : Fin n) : 0 ≤ sc g n p q := by
  unfold sc; simp only [Matrix.of_apply]; split_ifs <;> norm_num

lemma ext_le_one (g n : ℕ) (s u v : Fin (n + 1)) : simplicialCostExt g n s u v ≤ 1 := by
  unfold simplicialCostExt; simp only [Matrix.of_apply]; split_ifs <;> norm_num

lemma ext_nonneg (g n : ℕ) (s u v : Fin (n + 1)) : 0 ≤ simplicialCostExt g n s u v := by
  unfold simplicialCostExt; simp only [Matrix.of_apply]; split_ifs <;> norm_num

lemma ext_sub (g n : ℕ) (s : Fin (n + 1)) (p q : Fin n) :
    simplicialCostExt g n s (s.succAbove p) (s.succAbove q) = sc g n p q := by
  unfold simplicialCostExt sc
  simp only [Matrix.of_apply, Fin.insertNth_apply_succAbove]

end Aux_SDP2

end TSPSDPGap

open scoped Kronecker in
open TSPSDPGap TSPSDPGap.Aux_SDP2 in
theorem solution (g : ℕ) (hg : Even g) (hg2 : 2 ≤ g) :
    ∃ c : ℝ, ∀ n : ℕ, g ∣ n → g < n → ∀ r s : Fin (n + 1),
      sdp2Objective n (simplicialCostExt g n s) r s (Ymat g n) ≤ c / n + 2 := by
  refine ⟨8 * Real.pi ^ 2 * (g:ℝ) ^ 3, ?_⟩
  intro n hgn hlt r s
  have hn4 : 4 ≤ n := by
    obtain ⟨q, hq⟩ := hgn
    have hq2 : 2 ≤ q := by
      rcases Nat.lt_or_ge q 2 with h | h
      · interval_cases q <;> omega
      · exact h
    rw [hq]; nlinarith
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn0' : (n:ℝ) ≠ 0 := hn0.ne'
  have hY : ∀ a b, 0 ≤ Ymat g n a b := (c412 g n hg hg2 hgn hlt).2.2
  have hS1 := t421b g hg hg2 n hgn hlt
  unfold sdp2Objective
  rw [Matrix.add_mul, Matrix.trace_add]
  apply add_le_add
  · -- the Kronecker part
    refine le_trans ?_ hS1
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.kronecker_apply, Matrix.kroneckerMap_apply, Matrix.submatrix_apply,
      Matrix.smul_apply, smul_eq_mul, ext_sub]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro q _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro j _
    have h1 := csub_le n (by omega) r i j
    have h2 := sc_nonneg g n p q
    have h3 := hY (q, j) (p, i)
    have h4 := circ_nonneg' (n + 1) 1 (r.succAbove i) (r.succAbove j)
    calc sc g n p q * (1 / 2 * circBasis (n + 1) 1 (r.succAbove i) (r.succAbove j))
          * Ymat g n (q, j) (p, i)
        ≤ sc g n p q * (1 / 2 * circBasis n 1 i j) * Ymat g n (q, j) (p, i) := by
          refine mul_le_mul_of_nonneg_right ?_ h3
          refine mul_le_mul_of_nonneg_left ?_ h2
          linarith
      _ = 1 / 2 * (sc g n p q * circBasis n 1 i j * Ymat g n (q, j) (p, i)) := by ring
  · -- the diagonal part
    simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Fintype.sum_prod_type,
      Matrix.vec, Matrix.of_apply]
    have hdiag : ∀ x1 x2 : Fin n, Ymat g n (x1, x2) (x1, x2) = 1 / n := by
      intro x1 x2
      unfold Ymat
      simp only [Matrix.of_apply, eq_self_iff_true, if_true, ↓reduceIte]
      field_simp
    simp only [hdiag]
    have hcol := col_sum_le n r (by omega)
    calc ∑ x1 : Fin n, ∑ x2 : Fin n, circBasis (n + 1) 1 (r.succAbove x2) r *
            simplicialCostExt g n s s (s.succAbove x1) * (1 / (n:ℝ))
        ≤ ∑ _x1 : Fin n, ∑ x2 : Fin n, circBasis (n + 1) 1 (r.succAbove x2) r * (1 / (n:ℝ)) := by
          apply Finset.sum_le_sum; intro x1 _
          apply Finset.sum_le_sum; intro x2 _
          have h1 := ext_le_one g n s s (s.succAbove x1)
          have h2 := circ_nonneg' (n + 1) 1 (r.succAbove x2) r
          have h3 : (0:ℝ) ≤ 1 / (n:ℝ) := by positivity
          refine mul_le_mul_of_nonneg_right ?_ h3
          nlinarith
      _ = ∑ _x1 : Fin n, (∑ x2 : Fin n, circBasis (n + 1) 1 (r.succAbove x2) r) * (1 / (n:ℝ)) := by
          refine Finset.sum_congr rfl (fun x1 _ => ?_)
          rw [Finset.sum_mul]
      _ ≤ ∑ _x1 : Fin n, 2 * (1 / (n:ℝ)) := by
          apply Finset.sum_le_sum; intro x1 _
          exact mul_le_mul_of_nonneg_right hcol (by positivity)
      _ = 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
