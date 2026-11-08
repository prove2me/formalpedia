-- Prove2me | solution 1 for TSPSDPGap.lemma_4_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:04:53.712207+00:00
-- url     : https://prove2.me/submissions/ab8bcef2-d654-456e-87d6-4c8237d39197

import Mathlib
import Definitions.Def_TSPSDPGap_coeffA

namespace Aux_TSPl410

open Real

theorem tele (θ : ℝ) (K : ℕ) :
    2 * Real.sin (θ / 2) * ∑ i ∈ Finset.Icc 1 K, Real.cos ((i : ℝ) * θ) =
      Real.sin (((K : ℝ) + 1 / 2) * θ) - Real.sin (θ / 2) := by
  induction K with
  | zero => simp; ring_nf
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih, Real.two_mul_sin_mul_cos]
    have e1 : θ / 2 - ((K + 1 : ℕ) : ℝ) * θ = -(((K : ℝ) + 1 / 2) * θ) := by push_cast; ring
    have e2 : θ / 2 + ((K + 1 : ℕ) : ℝ) * θ = (((K + 1 : ℕ) : ℝ) + 1 / 2) * θ := by
      push_cast; ring
    rw [e1, e2, Real.sin_neg]
    ring

theorem cos_sum (m j : ℕ) (hm : 1 ≤ m) (hj0 : 0 < j) (hj : j < 2 * m) :
    ∑ i ∈ Finset.Icc 1 (m - 1), Real.cos (Real.pi * i * j / m) = -(1 + (-1 : ℝ) ^ j) / 2 := by
  set θ : ℝ := Real.pi * j / m with hθ
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcongr : ∀ i : ℕ, Real.cos (Real.pi * i * j / m) = Real.cos ((i : ℝ) * θ) := by
    intro i; congr 1; rw [hθ]; ring
  simp only [hcongr]
  have hs : 0 < Real.sin (θ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · rw [hθ]; have : (0 : ℝ) < j := by exact_mod_cast hj0
      positivity
    · rw [hθ]
      have hjR : (j : ℝ) < 2 * m := by exact_mod_cast hj
      rw [div_div, div_lt_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
  have ht := tele θ (m - 1)
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hm]; simp
  rw [hcast] at ht
  have harg : ((m : ℝ) - 1 + 1 / 2) * θ = (j : ℝ) * Real.pi - θ / 2 := by
    rw [hθ]; field_simp; ring
  rw [harg, Real.sin_nat_mul_pi_sub] at ht
  apply mul_left_cancel₀ (show 2 * Real.sin (θ / 2) ≠ 0 by positivity)
  rw [ht]
  ring

theorem lin_sum (g : ℕ) : ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) = g * (g - 1) / 2 := by
  induction g with
  | zero => simp
  | succ g ih =>
    rcases Nat.eq_zero_or_pos g with h | h
    · subst h; simp
    · rw [Finset.sum_Ico_succ_top (by omega)]
      have : ∑ j ∈ Finset.Ico 1 g, (((g + 1 : ℕ) : ℝ) - j) =
          ∑ j ∈ Finset.Ico 1 g, (((g : ℝ) - j) + 1) := by
        apply Finset.sum_congr rfl; intro j _; push_cast; ring
      rw [this, Finset.sum_add_distrib, ih, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
        Nat.cast_sub (by omega)]
      push_cast
      ring

end Aux_TSPl410

open Aux_TSPl410 in
theorem solution (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    ∑ i ∈ Finset.Icc 1 (n / 2), TSPSDPGap.coeffA g n i = 1 := by
  obtain ⟨g', hg'⟩ := hg
  obtain ⟨c, hc⟩ := hgn
  obtain ⟨m, hm⟩ : ∃ m, m = n / 2 := ⟨_, rfl⟩
  have hn2 : n = 2 * m := by
    rw [hm]
    have : n = 2 * (g' * c) := by rw [hc, hg']; ring
    omega
  have hm1 : 1 ≤ m := by omega
  have hgm : g < 2 * m := by omega
  rw [← hm]
  have hm' : m = (m - 1) + 1 := by omega
  rw [hm', Finset.sum_Icc_succ_top (by omega), ← hm']
  have hfirst : ∀ i ∈ Finset.Icc 1 (m - 1), TSPSDPGap.coeffA g n i =
      1 / ((n : ℝ) - g) * (2 + 4 / (g : ℝ) * ∑ j ∈ Finset.Ico 1 g,
        ((g : ℝ) - j) * Real.cos (Real.pi * i * j / m)) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    unfold TSPSDPGap.coeffA
    rw [← hm, if_pos (by omega)]
  have hmR : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < m := by exact_mod_cast hm1
    exact this.ne'
  have hcos : ∀ j : ℕ, Real.cos (Real.pi * (m : ℝ) * j / m) = (-1) ^ j := by
    intro j
    rw [show Real.pi * (m : ℝ) * j / m = (j : ℝ) * Real.pi by field_simp]
    exact Real.cos_nat_mul_pi j
  have hlast : TSPSDPGap.coeffA g n m =
      1 / ((n : ℝ) - g) * (1 + 2 / (g : ℝ) * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * (-1) ^ j) := by
    unfold TSPSDPGap.coeffA
    rw [← hm, if_neg (lt_irrefl m)]
    simp only [hcos]
  rw [Finset.sum_congr rfl hfirst, hlast]
  have hA : ∑ _i ∈ Finset.Icc 1 (m - 1), (2 : ℝ) = 2 * ((m : ℝ) - 1) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel, Nat.cast_sub hm1]
    push_cast
    ring
  have hB : ∑ i ∈ Finset.Icc 1 (m - 1), ∑ j ∈ Finset.Ico 1 g,
      ((g : ℝ) - j) * Real.cos (Real.pi * i * j / m) =
      ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * (-(1 + (-1 : ℝ) ^ j) / 2) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [← Finset.mul_sum, cos_sum m j hm1 (by omega) (by omega)]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hA, hB]
  have hsplit : ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * (-(1 + (-1 : ℝ) ^ j) / 2) =
      -(1 / 2) * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) -
        (1 / 2) * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * (-1) ^ j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsplit, lin_sum]
  generalize ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * (-1) ^ j = S2
  have hnR : (n : ℝ) = 2 * m := by exact_mod_cast hn2
  have hgR : (g : ℝ) < 2 * m := by exact_mod_cast hgm
  have hg0 : (g : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ g := by exact_mod_cast hg2
    linarith
  have hd : (2 * (m : ℝ) - g) ≠ 0 := by linarith
  rw [hnR]
  field_simp
  ring
