-- Prove2me | solution 1 for QuantumLinSys.Chebyshev.lemma_18
-- status  : ACCEPTED   (prove)
-- author  : @elem
-- created : 2026-10-09T21:58:08.38023+00:00
-- url     : https://prove2.me/submissions/befc05fd-6b93-4905-9125-d1d3df675240

import Mathlib
import Definitions.Def_QuantumLinSys_Chebyshev_Setting

open QuantumLinSys.Chebyshev

open Finset

/-- Telescoping product-to-sum identity:
`2 cos θ · Σ_{j<i} (-1)^j cos((2j+1)θ) = 1 - (-1)^i cos(2iθ)`. -/
lemma two_cos_mul_sum18 (θ : ℝ) (i : ℕ) :
    2 * Real.cos θ * ∑ j ∈ range i, (-1 : ℝ) ^ j * Real.cos ((2 * j + 1) * θ) =
      1 - (-1 : ℝ) ^ i * Real.cos (2 * i * θ) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [sum_range_succ, mul_add, ih]
    have h1 := Real.cos_add ((2 * i + 1) * θ) θ
    have h2 := Real.cos_sub ((2 * i + 1) * θ) θ
    have e1 : (2 * (i : ℝ) + 1) * θ + θ = 2 * ((i : ℝ) + 1) * θ := by ring
    have e2 : (2 * (i : ℝ) + 1) * θ - θ = 2 * (i : ℝ) * θ := by ring
    rw [e1] at h1
    rw [e2] at h2
    push_cast
    rw [pow_succ]
    linear_combination (-(-1 : ℝ) ^ i) * (h1 + h2)

/-- Swapping the double sum `Σ_{j<b} Σ_{i=j+1}^{b}` into `Σ_{i=1}^{b} Σ_{j<i}`. -/
lemma sum_swap18 (b : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ j ∈ range b, ∑ i ∈ Icc (j + 1) b, F i j = ∑ i ∈ Icc 1 b, ∑ j ∈ range i, F i j := by
  refine Finset.sum_comm' ?_
  intro j i
  simp only [mem_range, mem_Icc]
  omega

lemma sum_Icc_one18 (b : ℕ) (g : ℕ → ℝ) :
    ∑ i ∈ Icc 1 b, g i = ∑ i ∈ range b, g (i + 1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, sum_range_succ]

/-- Pairing the terms of a sum over `k = 0, …, 2b` of a symmetric function of `k - b`. -/
lemma sum_range_pair18 (f : ℤ → ℝ) (hf : ∀ m, f (-m) = f m) (b : ℕ) :
    ∑ k ∈ range (2 * b + 1), f ((k : ℤ) - b) = f 0 + 2 * ∑ i ∈ range b, f ((i : ℤ) + 1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have e1 : 2 * (b + 1) + 1 = (2 * b + 1) + 1 + 1 := by ring
    rw [e1, sum_range_succ', sum_range_succ]
    have e2 : ∀ k : ℕ, f (((k + 1 : ℕ) : ℤ) - ((b + 1 : ℕ) : ℤ)) = f ((k : ℤ) - b) := by
      intro k; exact congrArg f (by omega)
    simp only [e2]
    rw [ih, sum_range_succ]
    have e3 : f (((2 * b + 1 : ℕ) : ℤ) - (b : ℤ)) = f ((b : ℤ) + 1) := by
      exact congrArg f (by omega)
    have e4 : f (((0 : ℕ) : ℤ) - ((b + 1 : ℕ) : ℤ)) = f ((b : ℤ) + 1) := by
      rw [← hf]; exact congrArg f (by omega)
    rw [e3, e4]; ring

lemma natAbs_succ18 (i : ℕ) : ((i : ℤ) + 1).natAbs = i + 1 := by
  rw [← Nat.cast_succ, Int.natAbs_natCast]

/-- Matching a term of the binomial expansion with the symmetric pairing function. -/
lemma term_match18 (b k : ℕ) (hk : k < 2 * b + 1) (θ : ℝ) :
    (-1 : ℝ) ^ (k + b) * ((2 * b).choose k : ℝ) * Real.cos ((2 * (b : ℝ) - 2 * k) * θ) =
      (-1 : ℝ) ^ ((k : ℤ) - b).natAbs * ((2 * b).choose (b + ((k : ℤ) - b).natAbs) : ℝ) *
        Real.cos (2 * (((k : ℤ) - b : ℤ) : ℝ) * θ) := by
  have hcos : Real.cos ((2 * (b : ℝ) - 2 * k) * θ) =
      Real.cos (2 * (((k : ℤ) - b : ℤ) : ℝ) * θ) := by
    rw [← Real.cos_neg]; congr 1; push_cast; ring
  rw [hcos]
  rcases le_or_gt b k with hbk | hkb
  · have hm : ((k : ℤ) - b) = ((k - b : ℕ) : ℤ) := by
      rw [Nat.cast_sub hbk]
    rw [hm, Int.natAbs_natCast]
    have hs : (-1 : ℝ) ^ (k + b) = (-1) ^ (k - b) := by
      rw [show k + b = (k - b) + 2 * b by omega, pow_add, pow_mul]; simp
    rw [hs, show b + (k - b) = k by omega]
  · have hm : ((k : ℤ) - b) = -((b - k : ℕ) : ℤ) := by
      rw [Nat.cast_sub hkb.le]; ring
    rw [hm, Int.natAbs_neg, Int.natAbs_natCast]
    have hs : (-1 : ℝ) ^ (k + b) = (-1) ^ (b - k) := by
      rw [show k + b = (b - k) + 2 * k by omega, pow_add, pow_mul]; simp
    rw [hs, show b + (b - k) = 2 * b - k by omega, Nat.choose_symm (by omega)]

lemma term_match_one18 (b k : ℕ) (hk : k < 2 * b + 1) :
    ((2 * b).choose k : ℝ) = ((2 * b).choose (b + ((k : ℤ) - b).natAbs) : ℝ) := by
  rcases le_or_gt b k with hbk | hkb
  · have hm : ((k : ℤ) - b) = ((k - b : ℕ) : ℤ) := by
      rw [Nat.cast_sub hbk]
    rw [hm, Int.natAbs_natCast, show b + (k - b) = k by omega]
  · have hm : ((k : ℤ) - b) = -((b - k : ℕ) : ℤ) := by
      rw [Nat.cast_sub hkb.le]; ring
    rw [hm, Int.natAbs_neg, Int.natAbs_natCast, show b + (b - k) = 2 * b - k by omega,
      Nat.choose_symm (by omega)]

/-- The binomial expansion of `sin^{2b} θ` in cosines of multiples of `θ`. -/
lemma sin_pow_expand18 (θ : ℝ) (b : ℕ) :
    Real.sin θ ^ (2 * b) * 2 ^ (2 * b) =
      ∑ k ∈ range (2 * b + 1),
        (-1 : ℝ) ^ (k + b) * ((2 * b).choose k : ℝ) * Real.cos ((2 * (b : ℝ) - 2 * k) * θ) := by
  have key : Complex.sin θ ^ (2 * b) * 2 ^ (2 * b) =
      ∑ k ∈ range (2 * b + 1),
        (((-1 : ℝ) ^ (k + b) * ((2 * b).choose k : ℝ) : ℝ) : ℂ) *
          Complex.exp ((((2 * (b : ℝ) - 2 * k) * θ : ℝ) : ℂ) * Complex.I) := by
    have hI : Complex.I ^ (2 * b) = (-1) ^ b := by rw [pow_mul, Complex.I_sq]
    have hsin : Complex.sin θ ^ (2 * b) * 2 ^ (2 * b) = (2 * Complex.sin θ) ^ (2 * b) := by
      ring
    rw [hsin, Complex.two_sin, mul_pow, hI, sub_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    rw [mem_range] at hm
    have hz : Complex.exp (-(θ : ℂ) * Complex.I) ^ m * Complex.exp ((θ : ℂ) * Complex.I) ^ (2 * b - m) =
        Complex.exp ((((2 * (b : ℝ) - 2 * m) * θ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast [Nat.cast_sub (by omega : m ≤ 2 * b)]
      ring
    have hsign : (-1 : ℂ) ^ (m + 2 * b) * (-1) ^ b = (-1) ^ (m + b) := by
      rw [← pow_add, show m + 2 * b + b = (m + b) + 2 * b by omega, pow_add, pow_mul]; simp
    rw [← hz]
    push_cast
    rw [← hsign]
    ring
  have hL : ((Real.sin θ ^ (2 * b) * 2 ^ (2 * b) : ℝ) : ℂ) = Complex.sin θ ^ (2 * b) * 2 ^ (2 * b) := by
    push_cast; rfl
  have hre := congrArg Complex.re (hL.trans key)
  simp only [Complex.ofReal_re, Complex.re_sum, Complex.re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re] at hre
  exact hre

theorem solution (b : ℕ) : ∀ x ∈ Set.Icc (-1 : ℝ) 1, fTamed b x = chebSum b b x := by
  intro x hx
  set θ := Real.arccos x with hθ
  have hxθ : x = Real.cos θ := (Real.cos_arccos hx.1 hx.2).symm
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℝ, ∀ i, d i = ((2 * b).choose (b + i) : ℝ) / 2 ^ (2 * b) :=
    ⟨_, fun i => rfl⟩
  have hcoeff : ∀ j, coeff b j = ∑ i ∈ Icc (j + 1) b, d i := by
    intro j; unfold coeff; rw [Finset.sum_div]; apply sum_congr rfl; intro i _; rw [hd]
  have hcheb : chebSum b b x =
      4 * ∑ j ∈ range b, (-1 : ℝ) ^ j * coeff b j * Real.cos ((2 * j + 1) * θ) := by
    unfold chebSum
    congr 1
    apply sum_congr rfl
    intro j _
    rw [hxθ, Polynomial.Chebyshev.T_real_cos]
    push_cast
    ring_nf
  have hn := natAbs_succ18
  -- the expansion of sin^{2b}
  have hsin : 2 * ∑ i ∈ range b, (-1 : ℝ) ^ (i + 1) * d (i + 1) * Real.cos (2 * ((i : ℝ) + 1) * θ) =
      Real.sin θ ^ (2 * b) - d 0 := by
    have h1 := sin_pow_expand18 θ b
    have h2 := sum_range_pair18
      (fun m : ℤ => (-1 : ℝ) ^ m.natAbs * ((2 * b).choose (b + m.natAbs) : ℝ) *
        Real.cos (2 * (m : ℝ) * θ))
      (by intro m; simp only [Int.natAbs_neg, Int.cast_neg]; rw [show 2 * (-(m : ℝ)) * θ = -(2 * m * θ) by ring, Real.cos_neg]) b
    try simp only at h2
    rw [Finset.sum_congr rfl (fun k hk => term_match18 b k (mem_range.mp hk) θ)] at h1
    rw [h2] at h1
    simp only [hn, Int.natAbs_zero, add_zero, Int.cast_zero, mul_zero, zero_mul, Real.cos_zero,
      pow_zero, one_mul, mul_one, Int.cast_add, Int.cast_natCast, Int.cast_one] at h1
    have hs : ∑ i ∈ range b, (-1 : ℝ) ^ (i + 1) * d (i + 1) * Real.cos (2 * ((i : ℝ) + 1) * θ) =
        (∑ i ∈ range b, (-1 : ℝ) ^ (i + 1) * ((2 * b).choose (b + (i + 1)) : ℝ) *
          Real.cos (2 * ((i : ℝ) + 1) * θ)) / 2 ^ (2 * b) := by
      rw [Finset.sum_div]; apply sum_congr rfl; intro i _; simp only [hd]; ring
    rw [hs, hd 0, add_zero]
    have h2b : (2 : ℝ) ^ (2 * b) ≠ 0 := by positivity
    rw [mul_div_assoc', eq_sub_iff_add_eq, ← add_div, div_eq_iff h2b]
    linarith [h1]
  have hone : 2 * ∑ i ∈ range b, d (i + 1) = 1 - d 0 := by
    have h1 : (∑ m ∈ range (2 * b + 1), ((2 * b).choose m : ℝ)) = 2 ^ (2 * b) := by
      exact_mod_cast Nat.sum_range_choose (2 * b)
    have h2 := sum_range_pair18 (fun m : ℤ => ((2 * b).choose (b + m.natAbs) : ℝ))
      (by intro m; simp only [Int.natAbs_neg]) b
    try simp only at h2
    rw [Finset.sum_congr rfl (fun k hk => term_match_one18 b k (mem_range.mp hk))] at h1
    rw [h2] at h1
    simp only [hn, Int.natAbs_zero, add_zero] at h1
    have hs : ∑ i ∈ range b, d (i + 1) =
        (∑ i ∈ range b, ((2 * b).choose (b + (i + 1)) : ℝ)) / 2 ^ (2 * b) := by
      rw [Finset.sum_div]; apply sum_congr rfl; intro i _; rw [hd]
    rw [hs, hd 0, add_zero]
    have h2b : (2 : ℝ) ^ (2 * b) ≠ 0 := by positivity
    rw [mul_div_assoc', eq_sub_iff_add_eq, ← add_div, div_eq_iff h2b]
    linarith [h1]
  have hmain : 4 * Real.cos θ * ∑ j ∈ range b, (-1 : ℝ) ^ j * coeff b j * Real.cos ((2 * j + 1) * θ)
      = 1 - Real.sin θ ^ (2 * b) := by
    calc 4 * Real.cos θ * ∑ j ∈ range b, (-1 : ℝ) ^ j * coeff b j * Real.cos ((2 * j + 1) * θ)
        = 4 * Real.cos θ * ∑ j ∈ range b, ∑ i ∈ Icc (j + 1) b,
            (-1 : ℝ) ^ j * d i * Real.cos ((2 * j + 1) * θ) := by
          congr 1; apply sum_congr rfl; intro j _
          rw [hcoeff, Finset.mul_sum, Finset.sum_mul]
      _ = 4 * Real.cos θ * ∑ i ∈ Icc 1 b, ∑ j ∈ range i,
            (-1 : ℝ) ^ j * d i * Real.cos ((2 * j + 1) * θ) := by
          rw [sum_swap18]
      _ = ∑ i ∈ Icc 1 b, 2 * d i *
            (2 * Real.cos θ * ∑ j ∈ range i, (-1 : ℝ) ^ j * Real.cos ((2 * j + 1) * θ)) := by
          rw [Finset.mul_sum]; apply sum_congr rfl; intro i _
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]; apply sum_congr rfl; intro j _; ring
      _ = ∑ i ∈ Icc 1 b, 2 * d i * (1 - (-1 : ℝ) ^ i * Real.cos (2 * i * θ)) := by
          apply sum_congr rfl; intro i _; rw [two_cos_mul_sum18]
      _ = ∑ i ∈ range b, 2 * d (i + 1) *
            (1 - (-1 : ℝ) ^ (i + 1) * Real.cos (2 * ((i : ℝ) + 1) * θ)) := by
          rw [sum_Icc_one18]; apply sum_congr rfl; intro i _; push_cast; ring
      _ = 2 * ∑ i ∈ range b, d (i + 1) -
            2 * ∑ i ∈ range b, (-1 : ℝ) ^ (i + 1) * d (i + 1) * Real.cos (2 * ((i : ℝ) + 1) * θ) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply sum_congr rfl; intro i _; ring
      _ = 1 - Real.sin θ ^ (2 * b) := by rw [hone, hsin]; ring
  by_cases hc : Real.cos θ = 0
  · have hx0 : x = 0 := by rw [hxθ, hc]
    have hθ' : θ = Real.pi / 2 := by rw [hθ, hx0, Real.arccos_zero]
    rw [hcheb, hx0]
    unfold fTamed
    rw [div_zero]
    symm
    rw [mul_eq_zero]; right
    apply Finset.sum_eq_zero
    intro j _
    have hz : Real.cos ((2 * (j : ℝ) + 1) * θ) = 0 := by
      rw [hθ']
      exact Real.cos_eq_zero_iff.mpr ⟨j, by push_cast; ring⟩
    rw [hz, mul_zero]
  · rw [hcheb]
    unfold fTamed
    rw [hxθ]
    have hs2 : 1 - Real.cos θ ^ 2 = Real.sin θ ^ 2 := by rw [Real.sin_sq]
    rw [hs2, ← pow_mul, div_eq_iff hc, ← hmain]
    ring

