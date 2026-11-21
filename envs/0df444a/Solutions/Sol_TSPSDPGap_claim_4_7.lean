-- Prove2me | solution 1 for TSPSDPGap.claim_4_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:43:56.682629+00:00
-- url     : https://prove2.me/submissions/9b795ac7-d3f7-424d-be57-04bca09c0db1

import Mathlib
import Definitions.Def_TSPSDPGap_Ymat

namespace TSPSDPGap

namespace Aux_C47

open Finset

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

lemma circ_comb_total (n : ℕ) (c : ℕ → ℝ) :
    ∑ s : Fin n, ∑ t : Fin n, (∑ i ∈ Finset.Icc 1 (n / 2), c i • circBasis n i) s t
      = 2 * (n : ℝ) * ∑ i ∈ Finset.Icc 1 (n / 2), c i := by
  have hA : ∀ s t : Fin n, (∑ i ∈ Finset.Icc 1 (n / 2), c i • circBasis n i) s t
      = ∑ i ∈ Finset.Icc 1 (n / 2), c i * circBasis n i s t := by
    intro s t
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul]
  calc ∑ s : Fin n, ∑ t : Fin n, (∑ i ∈ Finset.Icc 1 (n / 2), c i • circBasis n i) s t
      = ∑ s : Fin n, ∑ t : Fin n, ∑ i ∈ Finset.Icc 1 (n / 2), c i * circBasis n i s t := by
        simp only [hA]
    _ = ∑ s : Fin n, ∑ i ∈ Finset.Icc 1 (n / 2), ∑ t : Fin n, c i * circBasis n i s t :=
        Finset.sum_congr rfl (fun s _ => Finset.sum_comm)
    _ = ∑ i ∈ Finset.Icc 1 (n / 2), ∑ s : Fin n, ∑ t : Fin n, c i * circBasis n i s t :=
        Finset.sum_comm
    _ = ∑ i ∈ Finset.Icc 1 (n / 2), c i * (2 * n) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi' := Finset.mem_Icc.mp hi
        have hin : i < n := by omega
        have : ∑ s : Fin n, ∑ t : Fin n, c i * circBasis n i s t
            = ∑ s : Fin n, c i * ∑ t : Fin n, circBasis n i s t :=
          Finset.sum_congr rfl (fun s _ => (Finset.mul_sum _ _ _).symm)
        rw [this]
        simp only [circ_row n i hi'.1 hin]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ = 2 * (n : ℝ) * ∑ i ∈ Finset.Icc 1 (n / 2), c i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring

lemma tel (θ : ℝ) (M : ℕ) (hM : 1 ≤ M) :
    2 * Real.sin (θ / 2) * ∑ i ∈ Finset.Ico 1 M, Real.cos (i * θ)
      = Real.sin ((M - 1 / 2) * θ) - Real.sin (θ / 2) := by
  induction M, hM using Nat.le_induction with
  | base =>
    simp only [Finset.Ico_self, Finset.sum_empty, mul_zero, Nat.cast_one]
    rw [show ((1:ℝ) - 1 / 2) * θ = θ / 2 by ring, sub_self]
  | succ M hM ih =>
    rw [Finset.sum_Ico_succ_top hM, mul_add, ih, Nat.cast_succ,
      show ((M:ℝ) + 1 - 1 / 2) * θ = M * θ + θ / 2 by ring,
      show ((M:ℝ) - 1 / 2) * θ = M * θ - θ / 2 by ring, Real.sin_add, Real.sin_sub]
    ring

lemma cos_sum (m j : ℕ) (hm : 1 ≤ m) (hj1 : 1 ≤ j) (hj2 : j < 2 * m) :
    2 * ∑ i ∈ Finset.Ico 1 m, Real.cos (Real.pi * i * j / m) + Real.cos (Real.pi * m * j / m)
      = -1 := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hj2R : (j:ℝ) < 2 * m := by exact_mod_cast hj2
  have hj1R : (1:ℝ) ≤ j := by exact_mod_cast hj1
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = Real.pi * j / m := ⟨_, rfl⟩
  have e1 : ∀ i : ℕ, Real.pi * (i:ℝ) * j / m = i * θ := by
    intro i; rw [hθ]; ring
  have hcm : Real.cos (Real.pi * (m:ℝ) * j / m) = Real.cos (j * Real.pi) := by
    rw [show Real.pi * (m:ℝ) * j / m = j * Real.pi * ((m:ℝ) / m) by ring, div_self hmR.ne',
      mul_one]
  rw [hcm]
  simp only [e1]
  have hsinpos : 0 < Real.sin (θ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · rw [hθ]
      exact div_pos (div_pos (mul_pos Real.pi_pos (by linarith)) hmR) (by norm_num)
    · rw [hθ, div_div, div_lt_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
  have htel := tel θ m hm
  have hmθ : ((m:ℝ) - 1 / 2) * θ = j * Real.pi - θ / 2 := by
    have : (m:ℝ) * θ = j * Real.pi := by
      rw [hθ, mul_div_assoc', div_eq_iff hmR.ne']; ring
    linear_combination this
  have hend : Real.sin (((m:ℝ) - 1 / 2) * θ) = -Real.cos (j * Real.pi) * Real.sin (θ / 2) := by
    rw [hmθ, Real.sin_sub, Real.sin_nat_mul_pi]
    ring
  have hprod : Real.sin (θ / 2) * (2 * ∑ i ∈ Finset.Ico 1 m, Real.cos (i * θ)
      + Real.cos (j * Real.pi) + 1) = 0 := by
    linear_combination htel + hend
  rcases mul_eq_zero.mp hprod with h | h
  · linarith
  · linarith

lemma gauss (g : ℕ) : 2 * ∑ j ∈ Finset.Ico 1 g, ((g:ℝ) - j) = g * ((g:ℝ) - 1) := by
  induction g with
  | zero => simp
  | succ g ih =>
    rcases Nat.eq_zero_or_pos g with h | h
    · subst h; simp
    · rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ g)]
      have e : ∑ j ∈ Finset.Ico 1 g, (((g + 1 : ℕ) : ℝ) - j)
          = ∑ j ∈ Finset.Ico 1 g, ((g:ℝ) - j) + ∑ j ∈ Finset.Ico 1 g, (1:ℝ) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        push_cast
        ring
      rw [e, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ g)]
      push_cast
      linear_combination ih

end Aux_C47

end TSPSDPGap

open TSPSDPGap TSPSDPGap.Aux_C47 in
theorem solution (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    Matrix.trace (Matrix.of (fun _ _ => (1 : ℝ)) * Ymat g n) = (n : ℝ) ^ 2 := by
  obtain ⟨q, hq⟩ := hgn
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with h | h
    · interval_cases q <;> omega
    · exact h
  have hn4 : 4 ≤ n := by rw [hq]; nlinarith
  have hneven : Even n := by rw [hq]; exact hg.mul_right q
  obtain ⟨m, hm⟩ : ∃ m, m = n / 2 := ⟨_, rfl⟩
  have hm2 : 2 * m = n := by rw [hm]; exact Nat.two_mul_div_two_of_even hneven
  have hm1 : 1 ≤ m := by omega
  have hm2R : 2 * (m:ℝ) = n := by exact_mod_cast hm2
  have hg0 : (0:ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hng : (0:ℝ) < (n:ℝ) - g := by
    have : (g:ℝ) < n := by exact_mod_cast hlt
    linarith
  have hg1 : (0:ℝ) < (g:ℝ) - 1 := by
    have : (2:ℝ) ≤ g := by exact_mod_cast hg2
    linarith
  have hn0 : (0:ℝ) < n := by linarith
  have hn0' : (n:ℝ) ≠ 0 := hn0.ne'
  have hIcc : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  -- the coefficient sums
  have hA_lt : ∀ i ∈ Finset.Ico 1 m, coeffA g n i = 1 / ((n:ℝ) - g) * (2 + 4 / (g:ℝ) *
      ∑ j ∈ Finset.Ico 1 g, ((g:ℝ) - j) * Real.cos (Real.pi * i * j / m)) := by
    intro i hi
    unfold coeffA
    rw [← hm, if_pos (Finset.mem_Ico.mp hi).2]
  have hA_m : coeffA g n m = 1 / ((n:ℝ) - g) * (1 + 2 / (g:ℝ) *
      ∑ j ∈ Finset.Ico 1 g, ((g:ℝ) - j) * Real.cos (Real.pi * m * j / m)) := by
    unfold coeffA
    rw [← hm, if_neg (lt_irrefl m)]
  obtain ⟨S1, hS1⟩ : ∃ S1 : ℝ, S1 = ∑ i ∈ Finset.Ico 1 m,
      ∑ j ∈ Finset.Ico 1 g, ((g:ℝ) - j) * Real.cos (Real.pi * i * j / m) := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ S2 : ℝ, S2 =
      ∑ j ∈ Finset.Ico 1 g, ((g:ℝ) - j) * Real.cos (Real.pi * m * j / m) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∑ j ∈ Finset.Ico 1 g, ((g:ℝ) - j) := ⟨_, rfl⟩
  have hGv : 2 * G = g * ((g:ℝ) - 1) := by rw [hG]; exact gauss g
  have hW : 2 * S1 + S2 = -G := by
    have hS1' : S1 = ∑ j ∈ Finset.Ico 1 g, ((g:ℝ) - j) *
        ∑ i ∈ Finset.Ico 1 m, Real.cos (Real.pi * i * j / m) := by
      rw [hS1, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
    rw [hS1', hS2, hG, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj := Finset.mem_Ico.mp hj
    have hc := cos_sum m j hm1 hj.1 (by omega)
    linear_combination ((g:ℝ) - j) * hc
  have hsumIco : ∑ i ∈ Finset.Ico 1 m, coeffA g n i
      = 1 / ((n:ℝ) - g) * (2 * ((m:ℝ) - 1) + 4 / (g:ℝ) * S1) := by
    rw [Finset.sum_congr rfl hA_lt, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      Nat.card_Ico, nsmul_eq_mul, ← Finset.mul_sum, Nat.cast_sub hm1, Nat.cast_one, hS1]
    ring
  have hsplitA : ∑ i ∈ Finset.Ico 1 m, coeffA g n i + coeffA g n m = 1 := by
    rw [hsumIco, hA_m, ← hS2]
    have e1 : (2 / (g:ℝ)) * G = (g:ℝ) - 1 := by
      rw [show (2 / (g:ℝ)) * G = (2 * G) / g by ring, hGv, mul_div_cancel_left₀ _ hg0.ne']
    calc 1 / ((n:ℝ) - g) * (2 * ((m:ℝ) - 1) + 4 / (g:ℝ) * S1)
          + 1 / ((n:ℝ) - g) * (1 + 2 / (g:ℝ) * S2)
        = 1 / ((n:ℝ) - g) * (2 * (m:ℝ) - 1 + (2 / (g:ℝ)) * (2 * S1 + S2)) := by ring
      _ = 1 / ((n:ℝ) - g) * ((n:ℝ) - g) := by
          rw [hW, mul_neg, e1]
          congr 1
          linarith
      _ = 1 := one_div_mul_cancel hng.ne'
  have hsumA : ∑ i ∈ Finset.Icc 1 (n / 2), coeffA g n i = 1 := by
    rw [← hm, hIcc, Finset.sum_Ico_succ_top hm1]
    exact hsplitA
  have hB_lt : ∀ i ∈ Finset.Ico 1 m, coeffB g n i
      = (2 * (g:ℝ) - ((n:ℝ) - g) * coeffA g n i) / ((n:ℝ) * ((g:ℝ) - 1)) := by
    intro i hi
    unfold coeffB
    rw [← hm, if_pos (Finset.mem_Ico.mp hi).2]
  have hB_m : coeffB g n m = ((g:ℝ) - ((n:ℝ) - g) * coeffA g n m) / ((n:ℝ) * ((g:ℝ) - 1)) := by
    unfold coeffB
    rw [← hm, if_neg (lt_irrefl m)]
  have hD : (n:ℝ) * ((g:ℝ) - 1) ≠ 0 := (mul_pos hn0 hg1).ne'
  have hsumB : ∑ i ∈ Finset.Icc 1 (n / 2), coeffB g n i = 1 := by
    rw [← hm, hIcc, Finset.sum_Ico_succ_top hm1, Finset.sum_congr rfl hB_lt, hB_m,
      ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
      ← Finset.mul_sum, Nat.cast_sub hm1, Nat.cast_one, ← add_div,
      div_eq_one_iff_eq hD]
    linear_combination (-((n:ℝ) - g)) * hsplitA + (g:ℝ) * hm2R
  -- total entry sums of the two blocks
  have hAtot : ∑ s : Fin n, ∑ t : Fin n, Amat g n s t = 2 * n := by
    unfold Amat
    rw [circ_comb_total, hsumA, mul_one]
  have hBtot : ∑ s : Fin n, ∑ t : Fin n, Bmat g n s t = 2 * n := by
    unfold Bmat
    rw [circ_comb_total, hsumB, mul_one]
  -- each block of `Y` sums to one
  have hinner : ∀ x1 y1 : Fin n, ∑ x2 : Fin n, ∑ y2 : Fin n, Ymat g n (x1, x2) (y1, y2) = 1 := by
    intro x1 y1
    unfold Ymat
    simp only [Matrix.of_apply]
    by_cases h1 : x1 = y1
    · simp only [h1, eq_self_iff_true, if_true, ↓reduceIte]
      have e : ∀ x2 : Fin n, ∑ y2 : Fin n, 1 / (2 * (n:ℝ)) * (if x2 = y2 then (2:ℝ) else 0)
          = 1 / (2 * (n:ℝ)) * 2 := by
        intro x2
        rw [← Finset.mul_sum, Finset.sum_ite_eq]
        simp
      rw [Finset.sum_congr rfl (fun x2 _ => e x2), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · simp only [h1, ↓reduceIte]
      by_cases h2 : (x1 : ℕ) / (n / g) = (y1 : ℕ) / (n / g)
      · simp only [h2, ↓reduceIte]
        have e : ∑ x2 : Fin n, ∑ y2 : Fin n, 1 / (2 * (n:ℝ)) * Amat g n x2 y2
            = 1 / (2 * (n:ℝ)) * ∑ x2 : Fin n, ∑ y2 : Fin n, Amat g n x2 y2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun x2 _ => (Finset.mul_sum _ _ _).symm)
        rw [e, hAtot]
        field_simp
      · simp only [h2, ↓reduceIte]
        have e : ∑ x2 : Fin n, ∑ y2 : Fin n, 1 / (2 * (n:ℝ)) * Bmat g n x2 y2
            = 1 / (2 * (n:ℝ)) * ∑ x2 : Fin n, ∑ y2 : Fin n, Bmat g n x2 y2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun x2 _ => (Finset.mul_sum _ _ _).symm)
        rw [e, hBtot]
        field_simp
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, one_mul]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl (fun b1 _ => Finset.sum_comm)]
  simp only [hinner]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring
