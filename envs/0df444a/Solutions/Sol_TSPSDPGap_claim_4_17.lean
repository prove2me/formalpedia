-- Prove2me | solution 1 for TSPSDPGap.claim_4_17
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:02:07.606612+00:00
-- url     : https://prove2.me/submissions/c30a62a1-a3b2-4d05-b23f-2c93321fa117

import Mathlib
import Definitions.Def_TSPSDPGap_aHat
import Definitions.Def_TSPSDPGap_bHat

namespace Aux_TSPSDP_417

lemma cos_sum_zero (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k < n) :
    ∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * i * k / n) = 0 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I * k / n) with hω
  have hω1 : ω ≠ 1 := by
    intro h
    rw [hω, Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have h2 : ((k : ℝ) / n : ℂ) = (m : ℂ) := by
      have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have : (2 * Real.pi * Complex.I : ℂ) * ((k : ℂ) / n) = (2 * Real.pi * Complex.I) * m := by
        rw [show (2 * Real.pi * Complex.I : ℂ) * ((k : ℂ) / n) = 2 * Real.pi * Complex.I * k / n by ring,
          hm]; ring
      have := mul_left_cancel₀ hpi this
      push_cast
      exact this
    have h3 : (k : ℝ) / n = m := by exact_mod_cast h2
    have h4 : (0 : ℝ) < k / n := div_pos (by exact_mod_cast (by omega : 0 < k)) hn
    have h5 : (k : ℝ) / n < 1 := by rw [div_lt_one hn]; exact_mod_cast hkn
    rw [h3] at h4 h5
    have h6 : (0 : ℤ) < m := by exact_mod_cast h4
    have h7 : m < (1 : ℤ) := by exact_mod_cast h5
    omega
  have hωn : ω ^ n = 1 := by
    rw [hω, ← Complex.exp_nat_mul]
    rw [Complex.exp_eq_one_iff]
    refine ⟨k, ?_⟩
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    push_cast
    field_simp
  have hgeom : ∑ i ∈ Finset.range n, ω ^ i = 0 := by
    rw [geom_sum_eq hω1, hωn, sub_self, zero_div]
  have hcos : ∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * i * k / n)
      = ∑ i ∈ Finset.range n, (ω ^ i).re := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hω, ← Complex.exp_nat_mul]
    have : (i : ℂ) * (2 * Real.pi * Complex.I * k / n)
        = ((2 * Real.pi * i * k / n : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_ofReal_mul_I_re]
  rw [hcos, ← Complex.re_sum, hgeom, Complex.zero_re]

end Aux_TSPSDP_417

open TSPSDPGap Aux_TSPSDP_417 in
theorem solution (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k < n) :
    bHat g n k = -((g : ℝ) / ((n : ℝ) * ((g : ℝ) - 1))) -
      ((n : ℝ) - g) / ((n : ℝ) * ((g : ℝ) - 1)) * aHat g n k := by
  obtain ⟨N, hN⟩ : ∃ N, n = 2 * N := by
    obtain ⟨r, hr⟩ := hg
    obtain ⟨s, hs⟩ := hgn
    exact ⟨r * s, by rw [hs, hr]; ring⟩
  have hn2 : n / 2 = N := by omega
  have hN1 : 1 ≤ N := by omega
  set F : ℕ → ℝ := fun i => Real.cos (2 * Real.pi * i * k / n) with hF
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  -- reflection symmetry
  have hrefl : ∀ j, j ≤ n → F (n - j) = F j := by
    intro j hj
    simp only [hF]
    rw [Nat.cast_sub hj]
    have : 2 * Real.pi * ((n : ℝ) - j) * k / n = (k : ℕ) * (2 * Real.pi) - 2 * Real.pi * j * k / n := by
      field_simp <;> ring
    have hs : Real.sin ((k : ℕ) * (2 * Real.pi)) = 0 := by
      rw [show ((k : ℕ) : ℝ) * (2 * Real.pi) = ((2 * k : ℕ) : ℝ) * Real.pi by push_cast; ring]
      exact Real.sin_nat_mul_pi _
    rw [this, Real.cos_sub, Real.cos_nat_mul_two_pi, hs]
    ring
  have hfull := cos_sum_zero n k hk1 hkn
  have hsplit : ∑ i ∈ Finset.range n, F i
      = F 0 + ∑ i ∈ Finset.Ico 1 N, F i + F N + ∑ i ∈ Finset.Ico (N + 1) n, F i := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : 1 ≤ n),
      ← Finset.sum_Ico_consecutive _ (by omega : 1 ≤ N) (by omega : N ≤ n),
      ← Finset.sum_Ico_consecutive _ (Nat.le_succ N) (by omega : N + 1 ≤ n)]
    have h01 : Finset.Ico 0 1 = ({0} : Finset ℕ) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
    have hNN : Finset.Ico N (N + 1) = ({N} : Finset ℕ) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
    rw [h01, hNN, Finset.sum_singleton, Finset.sum_singleton]
    ring
  have hrsum : ∑ i ∈ Finset.Ico (N + 1) n, F i = ∑ i ∈ Finset.Ico 1 N, F i := by
    have h := Finset.sum_Ico_reflect F 1 (m := N) (n := n) (by omega)
    rw [show n + 1 - N = N + 1 by omega, show n + 1 - 1 = n by omega] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro j hj
    exact hrefl j (by simp at hj; omega)
  have hF0 : F 0 = 1 := by simp [hF]
  have hkey : 2 * ∑ i ∈ Finset.Ico 1 N, F i + F N = -1 := by
    have : (∑ i ∈ Finset.range n, F i) = 0 := hfull
    rw [hsplit, hrsum, hF0] at this
    linarith
  -- the c-weighted sum
  have hc : ∑ i ∈ Finset.Icc 1 (n / 2), (if i < n / 2 then 2 * (g : ℝ) else g) * F i = -g := by
    rw [hn2, ← Finset.Ico_insert_right (by omega : 1 ≤ N), Finset.sum_insert (by simp)]
    rw [if_neg (lt_irrefl N)]
    have hin : ∀ i ∈ Finset.Ico 1 N, (if i < N then 2 * (g : ℝ) else g) * F i = 2 * (g : ℝ) * F i :=
      fun i hi => by rw [if_pos (Finset.mem_Ico.1 hi).2]
    rw [Finset.sum_congr rfl hin, ← Finset.mul_sum]
    linear_combination (g : ℝ) * hkey
  unfold bHat aHat
  set D := (n : ℝ) * ((g : ℝ) - 1) with hD
  have e : ∀ i, coeffB g n i * Real.cos (2 * Real.pi * i * k / n)
      = ((if i < n / 2 then 2 * (g : ℝ) else g) * F i) / D
        - ((n : ℝ) - g) / D * (coeffA g n i * Real.cos (2 * Real.pi * i * k / n)) := by
    intro i
    unfold coeffB
    simp only [hF]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_sub_distrib, ← Finset.sum_div,
    ← Finset.mul_sum, hc]
  ring
