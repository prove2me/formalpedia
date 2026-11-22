-- Prove2me | solution 1 for SchauderBasis.not_exists_schauderBasis_continuousMap_fourier
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:15:45.668804+00:00
-- url     : https://prove2.me/submissions/2f8f04eb-9681-4129-9459-f81426076498

import Mathlib

open Filter Topology MeasureTheory AddCircle ENNReal

set_option autoImplicit false

namespace Sol_SchauderBasis_not_exists_schauderBasis_continuousMap_fourier

lemma abs_sin_nat_mul_le (m : ℕ) (α : ℝ) : |Real.sin (m * α)| ≤ m * |Real.sin α| := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : Real.sin (((m + 1 : ℕ) : ℝ) * α)
        = Real.sin (m * α) * Real.cos α + Real.cos (m * α) * Real.sin α := by
      rw [← Real.sin_add]; push_cast; ring_nf
    rw [h]
    calc |Real.sin (m * α) * Real.cos α + Real.cos (m * α) * Real.sin α|
        ≤ |Real.sin (m * α) * Real.cos α| + |Real.cos (m * α) * Real.sin α| := abs_add_le _ _
      _ ≤ |Real.sin (m * α)| + |Real.sin α| := by
          apply add_le_add
          · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
          · rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)
      _ ≤ m * |Real.sin α| + |Real.sin α| := by linarith
      _ = ((m + 1 : ℕ) : ℝ) * |Real.sin α| := by push_cast; ring

lemma two_sin_mul_sum_sin (θ a : ℝ) (n : ℕ) :
    2 * Real.sin (θ / 2) * ∑ k ∈ Finset.range n, Real.sin ((a + k) * θ)
      = Real.cos ((a - 1 / 2) * θ) - Real.cos ((a + n - 1 / 2) * θ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 : Real.cos ((a + n - 1 / 2) * θ)
        = Real.cos ((a + n) * θ) * Real.cos (θ / 2) + Real.sin ((a + n) * θ) * Real.sin (θ / 2) := by
      rw [← Real.cos_sub]; ring_nf
    have h2 : Real.cos ((a + ((n + 1 : ℕ) : ℝ) - 1 / 2) * θ)
        = Real.cos ((a + n) * θ) * Real.cos (θ / 2) - Real.sin ((a + n) * θ) * Real.sin (θ / 2) := by
      rw [← Real.cos_add]; push_cast; ring_nf
    rw [h1, h2]; ring

lemma abs_sum_sin_le (θ a : ℝ) (n : ℕ) (hs : Real.sin (θ / 2) ≠ 0) :
    |∑ k ∈ Finset.range n, Real.sin ((a + k) * θ)| ≤ 1 / |Real.sin (θ / 2)| := by
  have h := two_sin_mul_sum_sin θ a n
  have hpos : 0 < |Real.sin (θ / 2)| := abs_pos.mpr hs
  rw [le_div_iff₀ hpos]
  have h2 : |2 * Real.sin (θ / 2) * ∑ k ∈ Finset.range n, Real.sin ((a + k) * θ)| ≤ 2 := by
    rw [h]
    calc _ ≤ |Real.cos ((a - 1 / 2) * θ)| + |Real.cos ((a + n - 1 / 2) * θ)| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
      _ = 2 := by norm_num
  rw [abs_mul, abs_mul, abs_two] at h2
  linarith

lemma abel_bound (w x : ℕ → ℝ) (B : ℝ) (hw : Antitone w) (hw0 : ∀ k, 0 ≤ w k)
    (hS : ∀ j, |∑ k ∈ Finset.range j, x k| ≤ B) (n : ℕ) :
    |∑ k ∈ Finset.range n, w k * x k| ≤ B * w 0 := by
  have key : ∀ n : ℕ, |∑ k ∈ Finset.range n, w k * x k - w n * ∑ k ∈ Finset.range n, x k|
      ≤ B * (w 0 - w n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : ∑ k ∈ Finset.range (n + 1), w k * x k - w (n + 1) * ∑ k ∈ Finset.range (n + 1), x k
          = (∑ k ∈ Finset.range n, w k * x k - w n * ∑ k ∈ Finset.range n, x k)
            + (w n - w (n + 1)) * ∑ k ∈ Finset.range (n + 1), x k := by
        simp only [Finset.sum_range_succ]; ring
      rw [e]
      have hd : 0 ≤ w n - w (n + 1) := sub_nonneg.mpr (hw (Nat.le_succ n))
      have h3 : |(w n - w (n + 1)) * ∑ k ∈ Finset.range (n + 1), x k| ≤ (w n - w (n + 1)) * B := by
        rw [abs_mul, abs_of_nonneg hd]; exact mul_le_mul_of_nonneg_left (hS _) hd
      calc _ ≤ |∑ k ∈ Finset.range n, w k * x k - w n * ∑ k ∈ Finset.range n, x k|
            + |(w n - w (n + 1)) * ∑ k ∈ Finset.range (n + 1), x k| := abs_add_le _ _
        _ ≤ B * (w 0 - w n) + (w n - w (n + 1)) * B := add_le_add ih h3
        _ = B * (w 0 - w (n + 1)) := by ring
  have h1 := key n
  have h2 : |w n * ∑ k ∈ Finset.range n, x k| ≤ w n * B := by
    rw [abs_mul, abs_of_nonneg (hw0 n)]; exact mul_le_mul_of_nonneg_left (hS n) (hw0 n)
  have e : ∑ k ∈ Finset.range n, w k * x k
      = (∑ k ∈ Finset.range n, w k * x k - w n * ∑ k ∈ Finset.range n, x k)
        + w n * ∑ k ∈ Finset.range n, x k := by ring
  rw [e]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ B * (w 0 - w n) + w n * B := add_le_add h1 h2
    _ = B * w 0 := by ring

lemma abs_sum_sin_div_le (θ : ℝ) (N : ℕ) :
    |∑ k ∈ Finset.range N, Real.sin ((k + 1) * θ) / (k + 1)| ≤ 3 := by
  set s := |Real.sin (θ / 2)| with hs_def
  have hs0 : 0 ≤ s := abs_nonneg _
  have hterm : ∀ k : ℕ, |Real.sin ((k + 1) * θ)| ≤ 2 * (k + 1) * s := by
    intro k
    have h := abs_sin_nat_mul_le (2 * (k + 1)) (θ / 2)
    have e : ((2 * (k + 1) : ℕ) : ℝ) * (θ / 2) = (k + 1) * θ := by push_cast; ring
    rw [e] at h
    calc _ ≤ _ := h
      _ = 2 * (k + 1) * s := by push_cast; ring
  have hhead : ∀ M : ℕ, |∑ k ∈ Finset.range M, Real.sin ((k + 1) * θ) / (k + 1)| ≤ 2 * M * s := by
    intro M
    calc _ ≤ ∑ k ∈ Finset.range M, |Real.sin ((k + 1) * θ) / (k + 1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range M, 2 * s := by
          apply Finset.sum_le_sum; intro k _
          have hk : (0 : ℝ) < k + 1 := by positivity
          rw [abs_div, abs_of_pos hk, div_le_iff₀ hk]
          have := hterm k; nlinarith
      _ = 2 * M * s := by simp; ring
  rcases eq_or_ne (Real.sin (θ / 2)) 0 with h0 | h0
  · have hs : s = 0 := by simp [hs_def, h0]
    have := hhead N
    rw [hs, mul_zero] at this
    linarith
  · have hspos : 0 < s := abs_pos.mpr h0
    set M := ⌊1 / s⌋₊ with hM
    have hMs : (M : ℝ) * s ≤ 1 := by
      have h1 : (M : ℝ) ≤ 1 / s := Nat.floor_le (one_div_nonneg.mpr hs0)
      calc (M : ℝ) * s ≤ (1 / s) * s := by gcongr
        _ = 1 := by field_simp
    have hMs' : 1 < ((M : ℝ) + 1) * s := by
      have h1 : 1 / s < (M : ℝ) + 1 := Nat.lt_floor_add_one (1 / s)
      calc (1 : ℝ) = (1 / s) * s := by field_simp
        _ < ((M : ℝ) + 1) * s := by gcongr
    rcases le_or_gt N M with hNM | hNM
    · have h1 := hhead N
      have h2 : (N : ℝ) * s ≤ M * s := by gcongr
      linarith
    · obtain ⟨L, rfl⟩ : ∃ L, N = M + L := ⟨N - M, by omega⟩
      rw [Finset.sum_range_add]
      have htail : |∑ k ∈ Finset.range L,
          Real.sin ((((M + k : ℕ) : ℝ) + 1) * θ) / (((M + k : ℕ) : ℝ) + 1)| ≤ 1 := by
        have hab := abel_bound (fun k : ℕ => 1 / ((M : ℝ) + 1 + k))
          (fun k : ℕ => Real.sin (((M : ℝ) + 1 + k) * θ)) (1 / s) ?_ ?_ ?_ L
        · have e : ∑ k ∈ Finset.range L,
              Real.sin ((((M + k : ℕ) : ℝ) + 1) * θ) / (((M + k : ℕ) : ℝ) + 1)
              = ∑ k ∈ Finset.range L, (fun k : ℕ => 1 / ((M : ℝ) + 1 + k)) k *
                  (fun k : ℕ => Real.sin (((M : ℝ) + 1 + k) * θ)) k := by
            apply Finset.sum_congr rfl; intro k _
            simp only
            push_cast
            rw [show (M : ℝ) + k + 1 = M + 1 + k by ring]
            ring
          rw [e]
          calc _ ≤ _ := hab
            _ = 1 / (((M : ℝ) + 1) * s) := by rw [Nat.cast_zero, add_zero]; field_simp
            _ ≤ 1 := by
                rw [div_le_one (by positivity)]; linarith
        · intro i j hij
          simp only
          apply one_div_le_one_div_of_le (by positivity)
          have : (i : ℝ) ≤ j := by exact_mod_cast hij
          linarith
        · intro k; positivity
        · intro j
          exact abs_sum_sin_le θ ((M : ℝ) + 1) j h0
      calc _ ≤ |∑ k ∈ Finset.range M, Real.sin ((k + 1) * θ) / (k + 1)|
            + |∑ k ∈ Finset.range L,
              Real.sin ((((M + k : ℕ) : ℝ) + 1) * θ) / (((M + k : ℕ) : ℝ) + 1)| := abs_add_le _ _
        _ ≤ 2 * M * s + 1 := add_le_add (hhead M) htail
        _ ≤ 3 := by linarith


open Complex in
lemma fourier_sub_fourier_apply (T : ℝ) [Fact (0 < T)] (N k : ℕ) (hk : k ≤ N) (t : ℝ) :
    fourier (T := T) (((N + k + 2 : ℕ) : ℤ)) (t : AddCircle T)
        - fourier (T := T) (((N - k : ℕ) : ℤ)) (t : AddCircle T)
      = Complex.exp (((N + 1 : ℝ) * (2 * Real.pi * t / T) : ℝ) * I)
        * (2 * I * ((Real.sin ((k + 1) * (2 * Real.pi * t / T)) : ℝ) : ℂ)) := by
  have hT : (T : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : 0 < T).ne'
  rw [fourier_coe_apply, fourier_coe_apply]
  set u : ℝ := (N + 1 : ℝ) * (2 * Real.pi * t / T)
  set v : ℝ := (k + 1) * (2 * Real.pi * t / T)
  have e1 : Complex.exp (2 * Real.pi * I * (((N + k + 2 : ℕ) : ℤ) : ℂ) * t / T)
      = Complex.exp (u * I) * Complex.exp (v * I) := by
    rw [← Complex.exp_add]; congr 1
    simp only [u, v]; push_cast; field_simp; ring
  have e2 : Complex.exp (2 * Real.pi * I * (((N - k : ℕ) : ℤ) : ℂ) * t / T)
      = Complex.exp (u * I) * Complex.exp (-(v * I)) := by
    rw [← Complex.exp_add]; congr 1
    simp only [u, v]
    rw [Int.natCast_sub hk]; push_cast; field_simp; ring
  rw [e1, e2, ← mul_sub]
  congr 1
  rw [← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    Complex.ofReal_sin]
  ring

lemma norm_fourier_test_le (T : ℝ) [Fact (0 < T)] (N : ℕ) :
    ‖∑ k ∈ Finset.range N, (1 / ((k : ℂ) + 1)) •
        (fourier (T := T) (((N + k + 2 : ℕ) : ℤ)) - fourier (T := T) (((N - k : ℕ) : ℤ)))‖ ≤ 6 := by
  rw [ContinuousMap.norm_le _ (by norm_num)]
  intro x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  set θ : ℝ := 2 * Real.pi * t / T
  have h : (∑ k ∈ Finset.range N, (1 / ((k : ℂ) + 1)) •
        (fourier (T := T) (((N + k + 2 : ℕ) : ℤ)) - fourier (T := T) (((N - k : ℕ) : ℤ))))
          (QuotientAddGroup.mk t)
      = Complex.exp (((N + 1 : ℝ) * θ : ℝ) * Complex.I) * (2 * Complex.I *
          ((∑ k ∈ Finset.range N, Real.sin ((k + 1) * θ) / (k + 1) : ℝ) : ℂ)) := by
    rw [ContinuousMap.sum_apply, Complex.ofReal_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkN : k ≤ N := (Finset.mem_range.mp hk).le
    rw [ContinuousMap.smul_apply, ContinuousMap.sub_apply, smul_eq_mul]
    have := fourier_sub_fourier_apply T N k hkN t
    erw [this]
    simp only [θ]
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, norm_mul,
    Complex.norm_real, Complex.norm_I, Complex.norm_two, mul_one, Real.norm_eq_abs]
  have := abs_sum_sin_div_le θ N
  linarith

end Sol_SchauderBasis_not_exists_schauderBasis_continuousMap_fourier

open Sol_SchauderBasis_not_exists_schauderBasis_continuousMap_fourier in
theorem solution (T : ℝ) [Fact (0 < T)] :
    ¬ ∃ b : SchauderBasis ℂ C(AddCircle T, ℂ),
      ∀ n : ℕ, b.basis n = fourier (T := T) (if Odd n then (((n + 1) / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) := by
  rintro ⟨b, hb⟩
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  have hpos : ∀ j : ℕ, fourier (T := T) ((j + 1 : ℕ) : ℤ) = b.basis (2 * j + 1) := by
    intro j
    rw [hb, if_pos (odd_two_mul_add_one j)]
    congr 2
    omega
  have hbound : ∀ N : ℕ, ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 1)) ≤ C * 6 := by
    intro N
    set ψ : C(AddCircle T, ℂ) := ∑ k ∈ Finset.range N, (1 / ((k : ℂ) + 1)) •
        (fourier (T := T) (((N + k + 2 : ℕ) : ℤ)) - fourier (T := T) (((N - k : ℕ) : ℤ))) with hψ
    have hproj : b.proj (2 * N + 1) ψ = ∑ k ∈ Finset.range N, (1 / ((k : ℂ) + 1)) •
        (0 - fourier (T := T) (((N - k : ℕ) : ℤ))) := by
      rw [hψ, map_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkN : k < N := Finset.mem_range.mp hk
      rw [map_smul, map_sub]
      congr 2
      · rw [show N + k + 2 = (N + k + 1) + 1 by omega, hpos, b.proj_apply_basis_mem,
          if_neg (by omega)]
      · rw [show N - k = (N - k - 1) + 1 by omega, hpos, b.proj_apply_basis_mem,
          if_pos (by omega)]
    have heval : (b.proj (2 * N + 1) ψ) 0
        = -((∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 1)) : ℝ) : ℂ) := by
      rw [hproj, ContinuousMap.sum_apply, Complex.ofReal_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContinuousMap.zero_apply,
        fourier_eval_zero, smul_eq_mul]
      push_cast; ring
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
    calc ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 1))
        = ‖(b.proj (2 * N + 1) ψ) 0‖ := by
          rw [heval, norm_neg, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Finset.sum_nonneg (fun k _ => by positivity))]
      _ ≤ ‖b.proj (2 * N + 1) ψ‖ := ContinuousMap.norm_coe_le_norm _ _
      _ ≤ ‖b.proj (2 * N + 1)‖ * ‖ψ‖ := (b.proj (2 * N + 1)).le_opNorm ψ
      _ ≤ C * 6 := mul_le_mul (hC _) (norm_fourier_test_le T N) (norm_nonneg _) hC0
  obtain ⟨N, hN⟩ :=
    (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop (C * 6)).exists
  exact absurd (hbound N) (not_le.mpr hN)
