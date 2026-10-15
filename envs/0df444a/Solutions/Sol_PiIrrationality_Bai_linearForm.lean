-- Prove2me | solution 1 for PiIrrationality.Bai.linearForm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T20:06:41.170699+00:00
-- url     : https://prove2.me/submissions/aa473f03-4c68-443e-b23f-ecbbd921ae85

import Definitions.Def_PiIrrationality_BaiForms
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Roots
set_option autoImplicit false

-- ===== inlined: scratch.research.campaign_pick.pi_stage2.BaiDefs =====
section
set_option autoImplicit false

/-!
# Bai's linear forms for π: objects (stage 2, private)

Y. Bai, "The irrationality measure of π is at most 7.101862832357", arXiv:2609.11276v2,
equations (1.8), (2.14), Section 2 and (4.4)-(4.5).

`PiIrrationality.BaiGen` holds the objects for VARIABLE exponents `(a, b, c)`; every arithmetic
lemma is proved there and specialised at the end. `PiIrrationality.Bai` is the specialisation
`(a, b, c) = (1857, 3714, 5570)`, `d₀ = 2a + 4b - 2c = 7430`, `h = 5b - 5c/2 = 4645`, written out the
way the Definition file will be posted (moona3k's 01b4e42c is the `(2,4,6)` template), with `rfl`
bridges to the general objects.

## Laurent coefficients
With `t = 10w - 5` one has `5 + t = 10w`, `5 - t = 10(1-w)`, `t² = 25(2w-1)²` and
`t⁴ + 6t² + 25 = 400 Q(w)` with `Q(w) = 25w⁴ - 50w³ + 39w² - 14w + 2`, hence
`R_n(t) = 2^{4bn-2cn-2} 5^{2an+2bn-2cn-1} G_n(w) / w^{cn+1}`, where
`G_n(w) = (2w-1)^{2an} Q(w)^{bn} (1-w)^{-(cn+1)}` is a power series with integer coefficients `g_{n,m}`.
The coefficient of `(5+t)^{-(j+1)}` in the Laurent expansion of `R_n` at `t = -5` is therefore
`c_{j,n} = 2^{(4b-2c)n+j-1} 5^{(2a+2b-2c)n+j} g_{n, cn-j}` for `j ≤ cn` (and `0` for `j > cn`).
`R_n` is even, so the coefficients at `t = 5` (of `(5-t)^{-(j+1)}`) are the same numbers.
At `j = 0`: `c_{0,n} = 2^{(4b-2c)n-1} 5^{2(a+b-c)n} g_{n,cn}`, and `g_{n,cn} = (-1)^{cn} coef_n`
(substitution `w = -z/(1-z)`; checked numerically in `check_defs.py`, proved in a later stage).
-/

namespace PiIrrationality.BaiGen

open Complex Polynomial

variable (a b c : ℕ)

/-- `R_n(t) = 5 t^{2an} (t^4+6t^2+25)^{bn} / (25-t^2)^{cn+1}`. -/
noncomputable def R (n : ℕ) (t : ℂ) : ℂ :=
  5 * t ^ (2 * a * n) * (t ^ 4 + 6 * t ^ 2 + 25) ^ (b * n) / (25 - t ^ 2) ^ (c * n + 1)

/-- `J_n = i ∫_{-1-2i}^{-1+2i} R_n(t) dt` along `t = -1 + i s`, `-2 ≤ s ≤ 2`. -/
noncomputable def J (n : ℕ) : ℂ :=
  -∫ s in (-2 : ℝ)..2, R a b c n (-1 + (s : ℂ) * I)

/-- `d₀ = 2a + 4b - 2c` (the degree of the polynomial part is `d₀ n - 2`). -/
def d0 : ℕ := 2 * a + 4 * b - 2 * c

/-- `h = 5b - 5c/2` (for even `c`). -/
def h : ℕ := 5 * b - 5 * c / 2

/-- `A(z) = (1+z)^{2a} P(z)^b`, `P(z) = (z²+2z+2)(2z²+2z+1) = 2 + 6z + 9z² + 6z³ + 2z⁴`. -/
noncomputable def A : ℕ[X] :=
  (1 + X) ^ (2 * a) * (C 2 + C 6 * X + C 9 * X ^ 2 + C 6 * X ^ 3 + C 2 * X ^ 4) ^ b

/-- `coef n = [z^{cn}] A(z)^n (1-z)^{-d₀ n}`. -/
noncomputable def coef (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (c * n + 1),
    (A a b ^ n).coeff k * Nat.choose (d0 a b c * n - 1 + (c * n - k)) (c * n - k)

/-- Bai's deleted primes (2.14): primes `p` with `max(5, √(d₀n)) < p ≤ d₀n` and
`{an/p + 1/2} + 2{bn/p} < {cn/p}`. -/
def deletedPrimes (n : ℕ) : Finset ℕ :=
  (Finset.range (d0 a b c * n + 1)).filter fun p =>
    p.Prime ∧ 5 < p ∧ d0 a b c * n < p ^ 2 ∧
      Int.fract (((a * n : ℕ) : ℚ) / p + 1 / 2) + 2 * Int.fract (((b * n : ℕ) : ℚ) / p) <
        Int.fract (((c * n : ℕ) : ℚ) / p)

/-- `Φ_n = ∏_{p ∈ P_n} p`. -/
def Phi (n : ℕ) : ℕ := ∏ p ∈ deletedPrimes a b c n, p

/-- `M_n = 2^{4 - hn} lcm(1,…,d₀n) / Φ_n`. -/
noncomputable def M (n : ℕ) : ℝ :=
  2 ^ 4 * (Nat.lcmUpto (d0 a b c * n) : ℝ) / (2 ^ (h b c * n) * (Phi a b c n : ℝ))

/-- `Q(w) = 25w⁴ - 50w³ + 39w² - 14w + 2`, so `t⁴ + 6t² + 25 = 400 Q(w)` at `t = 10w - 5`. -/
noncomputable def Qw : ℤ[X] :=
  25 * X ^ 4 - 50 * X ^ 3 + 39 * X ^ 2 - 14 * X + 2

/-- The numerator `H_n(w) = (2w-1)^{2an} Q(w)^{bn}`. -/
noncomputable def Hw (n : ℕ) : ℤ[X] := (2 * X - 1) ^ (2 * a * n) * Qw ^ (b * n)

/-- `G_n(w) = H_n(w) (1-w)^{-(cn+1)}` as an integer power series. -/
noncomputable def Gw (n : ℕ) : PowerSeries ℤ :=
  (Hw a b n : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (c * n + 1)).val

/-- `g_{n,m} = [w^m] G_n(w)`. -/
noncomputable def g (n m : ℕ) : ℤ := PowerSeries.coeff m (Gw a b c n)

/-- The Laurent coefficient `c_{j,n}` of `R_n` at `t = -5`: the coefficient of `(5+t)^{-(j+1)}`. -/
noncomputable def lc (n : ℕ) (j : ℤ) : ℚ :=
  if j ≤ ((c * n : ℕ) : ℤ) then
    (2 : ℚ) ^ (((4 * b * n : ℕ) : ℤ) - ((2 * c * n : ℕ) : ℤ) + j - 1) *
      (5 : ℚ) ^ (((2 * a * n + 2 * b * n : ℕ) : ℤ) - ((2 * c * n : ℕ) : ℤ) + j) *
      (g a b c n (((c * n : ℕ) : ℤ) - j).toNat : ℚ)
  else 0

end PiIrrationality.BaiGen

namespace PiIrrationality.Bai

open Complex Polynomial

/-- `g_{n,m}` at Bai's exponents. -/
noncomputable def g (n m : ℕ) : ℤ := BaiGen.g 1857 3714 5570 n m

/-- The Laurent coefficients `c_{j,n}` at Bai's exponents. -/
noncomputable def lc (n : ℕ) (j : ℤ) : ℚ := BaiGen.lc 1857 3714 5570 n j

theorem d0_eq : BaiGen.d0 1857 3714 5570 = 7430 := rfl

theorem h_eq : BaiGen.h 3714 5570 = 4645 := rfl

theorem R_eq (n : ℕ) (t : ℂ) : R n t = BaiGen.R 1857 3714 5570 n t := rfl

theorem J_eq (n : ℕ) : J n = BaiGen.J 1857 3714 5570 n := rfl

theorem A_eq : A = BaiGen.A 1857 3714 := by
  unfold A BaiGen.A
  rw [show 2 * 1857 = 3714 from rfl]

theorem coef_eq (n : ℕ) : coef n = BaiGen.coef 1857 3714 5570 n := by
  unfold coef BaiGen.coef
  rw [← A_eq, d0_eq]

theorem deletedPrimes_eq (n : ℕ) : deletedPrimes n = BaiGen.deletedPrimes 1857 3714 5570 n := rfl

theorem Phi_eq (n : ℕ) : Phi n = BaiGen.Phi 1857 3714 5570 n := rfl

theorem M_eq (n : ℕ) : M n = BaiGen.M 1857 3714 5570 n := by
  unfold M BaiGen.M
  rw [d0_eq, h_eq, ← Phi_eq]

/-- The explicit form of `c_{j,n}` at Bai's exponents:
`c_{j,n} = 2^{3716n + j - 1} 5^{2n + j} g_{n, 5570n - j}` for `j ≤ 5570 n`. -/
theorem lc_eq (n : ℕ) (j : ℤ) :
    lc n j = if j ≤ ((5570 * n : ℕ) : ℤ) then
      (2 : ℚ) ^ (3716 * (n : ℤ) + j - 1) * (5 : ℚ) ^ (2 * (n : ℤ) + j) *
        (g n (((5570 * n : ℕ) : ℤ) - j).toNat : ℚ)
    else 0 := by
  unfold lc BaiGen.lc g
  split_ifs with hj
  · congr 3 <;> push_cast <;> ring
  · rfl

end PiIrrationality.Bai
end

-- ===== inlined: scratch.research.campaign_pick.pi_stage2.PartialFrac =====
section
set_option autoImplicit false

/-!
# Partial fractions in `w` (stage 2, private)

For a numerator `H ∈ ℤ[w]` with `H(1-w) = H(w)` and any `N`, put `G = H (1-w)^{-(N+1)}`,
`g_i = [w^i] G` and `T(w) = Σ_{i ≤ N} g_i w^i`. Then
`H = Q (w(1-w))^{N+1} + (1-w)^{N+1} T(w) + w^{N+1} T(1-w)` with `Q ∈ ℤ[w]`,
`q_k = g_{N+1+k} - Σ_{i ≤ N} g_i C(N-i+k, N-i)` and `deg Q + 2(N+1) ≤ max(deg H, 2N+1)`.
This is the polynomial part of `H/(w(1-w))^{N+1}`; at `H = H_n`, `N = cn` it is Bai's `P_n` in the
variable `w = (t+5)/10`.
-/

namespace PiIrrationality.BaiPF

open Polynomial

section Generic

variable (H : ℤ[X]) (N : ℕ)

/-- `G = H (1-w)^{-(N+1)}`. -/
noncomputable def Gs : PowerSeries ℤ :=
  (H : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (N + 1)).val

/-- `g_i = [w^i] G`. -/
noncomputable def gc (i : ℕ) : ℤ := PowerSeries.coeff i (Gs H N)

/-- `T(w) = Σ_{i ≤ N} g_i w^i`. -/
noncomputable def T : ℤ[X] := ∑ i ∈ Finset.range (N + 1), C (gc H N i) * X ^ i

/-- The pole part `(1-w)^{N+1} T(w) + w^{N+1} T(1-w)`. -/
noncomputable def Rem : ℤ[X] := (1 - X) ^ (N + 1) * T H N + X ^ (N + 1) * (T H N).comp (1 - X)

/-- `F = H - Rem`. -/
noncomputable def F : ℤ[X] := H - Rem H N

/-- The polynomial part: `F = (w(1-w))^{N+1} Q` (when `H` is symmetric). -/
noncomputable def Qp : ℤ[X] := by
  classical
  exact if h : ∃ Q : ℤ[X], F H N = (X * (1 - X)) ^ (N + 1) * Q then Classical.choose h else 0

theorem coeff_T (j : ℕ) : (T H N).coeff j = if j < N + 1 then gc H N j else 0 := by
  simp only [T, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range]

theorem T_comp_one_sub : (T H N).comp (1 - X) =
    ∑ i ∈ Finset.range (N + 1), C (gc H N i) * (1 - X) ^ i := by
  rw [T, ← coe_compRingHom_apply, map_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [coe_compRingHom_apply, mul_comp, C_comp, pow_comp, X_comp]

theorem natDegree_T_le : (T H N).natDegree ≤ N := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_T, if_neg]
  have : N < j := by exact_mod_cast hj
  omega

theorem coe_one_sub_pow_mul_inv :
    (((1 - X) ^ (N + 1) : ℤ[X]) : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (N + 1)).val = 1 := by
  rw [Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X,
    ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
  exact (PowerSeries.invOneSubPow ℤ (N + 1)).inv_val

theorem X_pow_dvd_H_sub : X ^ (N + 1) ∣ H - (1 - X) ^ (N + 1) * T H N := by
  rw [X_pow_dvd_iff]
  intro d hd
  have hH : (H : PowerSeries ℤ) = (((1 - X) ^ (N + 1) : ℤ[X]) : PowerSeries ℤ) * Gs H N := by
    rw [Gs, mul_left_comm, coe_one_sub_pow_mul_inv, mul_one]
  have e1 : H.coeff d =
      PowerSeries.coeff d ((((1 - X) ^ (N + 1) : ℤ[X]) : PowerSeries ℤ) * Gs H N) := by
    rw [← hH, Polynomial.coeff_coe]
  rw [coeff_sub, e1, PowerSeries.coeff_mul, coeff_mul, sub_eq_zero]
  apply Finset.sum_congr rfl
  intro x hx
  have hx2 : x.1 + x.2 = d := Finset.mem_antidiagonal.1 hx
  rw [Polynomial.coeff_coe, coeff_T, if_pos (show x.2 < N + 1 by omega), gc]

theorem X_pow_dvd_F : X ^ (N + 1) ∣ F H N := by
  unfold F Rem
  rw [← sub_sub]
  exact dvd_sub (X_pow_dvd_H_sub H N) (dvd_mul_right _ _)

theorem F_comp_one_sub (hsym : H.comp (1 - X) = H) : (F H N).comp (1 - X) = F H N := by
  have h1 : ((1 : ℤ[X]) - X).comp (1 - X) = X := by simp
  unfold F Rem
  simp only [sub_comp, add_comp, mul_comp, pow_comp, X_comp, comp_assoc, h1, comp_X, hsym]
  ring

theorem one_sub_pow_dvd_F (hsym : H.comp (1 - X) = H) : (1 - X) ^ (N + 1) ∣ F H N := by
  obtain ⟨M, hM⟩ := X_pow_dvd_F H N
  refine ⟨M.comp (1 - X), ?_⟩
  rw [← F_comp_one_sub H N hsym, hM, mul_comp, pow_comp, X_comp]

theorem exists_Q (hsym : H.comp (1 - X) = H) :
    ∃ Q : ℤ[X], F H N = (X * (1 - X)) ^ (N + 1) * Q := by
  have hc : IsCoprime ((X : ℤ[X]) ^ (N + 1)) ((1 - X) ^ (N + 1)) :=
    (show IsCoprime (X : ℤ[X]) (1 - X) from ⟨1, 1, by ring⟩).pow
  rw [mul_pow]
  exact hc.mul_dvd (X_pow_dvd_F H N) (one_sub_pow_dvd_F H N hsym)

theorem F_eq (hsym : H.comp (1 - X) = H) : F H N = (X * (1 - X)) ^ (N + 1) * Qp H N := by
  have h := exists_Q H N hsym
  rw [Qp, dif_pos h]
  exact Classical.choose_spec h

/-- The partial-fraction identity. -/
theorem pf_identity (hsym : H.comp (1 - X) = H) :
    H = (X * (1 - X)) ^ (N + 1) * Qp H N + Rem H N := by
  rw [← F_eq H N hsym, F]; ring

theorem natDegree_Rem_le : (Rem H N).natDegree ≤ 2 * N + 1 := by
  have hT := natDegree_T_le H N
  have h1 : ((1 : ℤ[X]) - X).natDegree ≤ 1 := by compute_degree!
  unfold Rem
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_mul_le).trans ?_
    have hp1 : ((1 - X : ℤ[X]) ^ (N + 1)).natDegree ≤ N + 1 :=
      (natDegree_pow_le).trans (by simpa using Nat.mul_le_mul_left (N + 1) h1)
    omega
  · refine (natDegree_mul_le).trans ?_
    have h2 : ((T H N).comp (1 - X)).natDegree ≤ N :=
      (natDegree_comp_le).trans (by simpa using Nat.mul_le_mul hT h1)
    have : ((X : ℤ[X]) ^ (N + 1)).natDegree ≤ N + 1 := by
      rw [natDegree_X_pow]
    omega

theorem natDegree_Qp_le (hsym : H.comp (1 - X) = H) :
    (Qp H N).natDegree ≤ H.natDegree - 2 * (N + 1) := by
  by_cases hQ : Qp H N = 0
  · rw [hQ, natDegree_zero]; omega
  have hD : ((X : ℤ[X]) * (1 - X)) ^ (N + 1) ≠ 0 := by
    apply pow_ne_zero
    intro h
    have := congrArg (Polynomial.eval 2) h
    simp at this
  have hdeg : (((X : ℤ[X]) * (1 - X)) ^ (N + 1)).natDegree = 2 * (N + 1) := by
    rw [natDegree_pow]
    have : ((X : ℤ[X]) * (1 - X)).natDegree = 2 := by
      have e : (X : ℤ[X]) * (1 - X) = -X ^ 2 + X := by ring
      rw [e]; compute_degree!
    rw [this]; ring
  have hF := F_eq H N hsym
  have h1 : (F H N).natDegree = 2 * (N + 1) + (Qp H N).natDegree := by
    rw [hF, natDegree_mul hD hQ, hdeg]
  have h2 : (F H N).natDegree ≤ max H.natDegree (2 * N + 1) := by
    unfold F
    exact (natDegree_sub_le _ _).trans (max_le_max le_rfl (natDegree_Rem_le H N))
  omega

/-- The coefficients of the polynomial part. -/
theorem coeff_Qp (hsym : H.comp (1 - X) = H) (k : ℕ) :
    (Qp H N).coeff k = gc H N (N + 1 + k) -
      ∑ i ∈ Finset.range (N + 1), gc H N i * ((N - i + k).choose (N - i) : ℤ) := by
  set inv := (PowerSeries.invOneSubPow ℤ (N + 1)).val with hinv
  have hpf := congrArg (fun p : ℤ[X] => (p : PowerSeries ℤ) * inv) (pf_identity H N hsym)
  -- the image of `(1-w)^{N+1}` cancels
  have hu := coe_one_sub_pow_mul_inv N
  have e2 : (((1 - X) ^ (N + 1) * T H N : ℤ[X]) : PowerSeries ℤ) * inv = (T H N : PowerSeries ℤ) := by
    rw [Polynomial.coe_mul, mul_right_comm, hu, one_mul]
  have e1 : ((((X * (1 - X)) ^ (N + 1) * Qp H N : ℤ[X])) : PowerSeries ℤ) * inv =
      PowerSeries.X ^ (N + 1) * (Qp H N : PowerSeries ℤ) := by
    have : ((((X * (1 - X)) ^ (N + 1) * Qp H N : ℤ[X])) : PowerSeries ℤ) * inv =
        ((X ^ (N + 1) : ℤ[X]) : PowerSeries ℤ) * (Qp H N : PowerSeries ℤ) *
          ((((1 - X) ^ (N + 1) : ℤ[X]) : PowerSeries ℤ) * inv) := by
      rw [mul_pow, Polynomial.coe_mul, Polynomial.coe_mul]; ring
    rw [this, hu, mul_one, Polynomial.coe_pow, Polynomial.coe_X]
  have e3 : (((X ^ (N + 1) * (T H N).comp (1 - X) : ℤ[X])) : PowerSeries ℤ) * inv =
      PowerSeries.X ^ (N + 1) * ((((T H N).comp (1 - X) : ℤ[X]) : PowerSeries ℤ) * inv) := by
    rw [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, mul_assoc]
  have hG : Gs H N = PowerSeries.X ^ (N + 1) * (Qp H N : PowerSeries ℤ) + (T H N : PowerSeries ℤ) +
      PowerSeries.X ^ (N + 1) * ((((T H N).comp (1 - X) : ℤ[X]) : PowerSeries ℤ) * inv) := by
    rw [Gs, ← hinv, hpf, Rem, Polynomial.coe_add, Polynomial.coe_add, add_mul, add_mul,
      e1, e2, e3]
    ring
  -- coefficient `N+1+k`
  have hc := congrArg (PowerSeries.coeff (N + 1 + k)) hG
  rw [map_add, map_add, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
    if_pos (show N + 1 ≤ N + 1 + k by omega), if_pos (show N + 1 ≤ N + 1 + k by omega),
    show N + 1 + k - (N + 1) = k by omega, Polynomial.coeff_coe, Polynomial.coeff_coe, coeff_T,
    if_neg (show ¬ (N + 1 + k < N + 1) by omega), add_zero] at hc
  -- the coefficients of `T(1-w) (1-w)^{-(N+1)}`
  have hT1 : (((T H N).comp (1 - X) : ℤ[X]) : PowerSeries ℤ) * inv =
      ∑ i ∈ Finset.range (N + 1), PowerSeries.C (gc H N i) *
        (PowerSeries.invOneSubPow ℤ (N - i + 1)).val := by
    have hcomp := T_comp_one_sub H N
    rw [hcomp, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X, mul_assoc,
      hinv, show N + 1 = (N - i + 1) + i by omega,
      PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val]
  rw [hT1, map_sum] at hc
  have hsum : ∑ i ∈ Finset.range (N + 1), PowerSeries.coeff k (PowerSeries.C (gc H N i) *
        (PowerSeries.invOneSubPow ℤ (N - i + 1)).val) =
      ∑ i ∈ Finset.range (N + 1), gc H N i * ((N - i + k).choose (N - i) : ℤ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [PowerSeries.coeff_C_mul, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
      PowerSeries.coeff_mk]
  rw [hsum] at hc
  have hg : gc H N (N + 1 + k) = PowerSeries.coeff (N + 1 + k) (Gs H N) := rfl
  rw [hg]
  linarith

end Generic

/-! ## Bai's numerator is symmetric -/

section Bai

open PiIrrationality.BaiGen

theorem Qw_comp : (Qw).comp (1 - X) = Qw := by
  unfold Qw
  simp only [sub_comp, add_comp, mul_comp, pow_comp, X_comp, ofNat_comp, Nat.cast_ofNat]
  ring

theorem Hw_comp (a b n : ℕ) : (Hw a b n).comp (1 - X) = Hw a b n := by
  unfold Hw
  rw [mul_comp, pow_comp, pow_comp, Qw_comp]
  have h : ((2 : ℤ[X]) * X - 1).comp (1 - X) = -(2 * X - 1) := by
    simp only [sub_comp, mul_comp, X_comp, ofNat_comp, one_comp, Nat.cast_ofNat]; ring
  rw [h, Even.neg_pow ⟨a * n, by ring⟩]

theorem natDegree_Hw_le (a b n : ℕ) : (Hw a b n).natDegree ≤ 2 * a * n + 4 * (b * n) := by
  unfold Hw
  have h1 : ((2 : ℤ[X]) * X - 1).natDegree ≤ 1 := by compute_degree!
  have h2 : (Qw).natDegree ≤ 4 := by unfold Qw; compute_degree!
  refine (natDegree_mul_le).trans (add_le_add ?_ ?_)
  · exact (natDegree_pow_le).trans (by simpa using Nat.mul_le_mul_left (2 * a * n) h1)
  · refine (natDegree_pow_le).trans ?_
    have := Nat.mul_le_mul_left (b * n) h2
    linarith

theorem gc_eq (a b c n i : ℕ) : gc (Hw a b n) (c * n) i = g a b c n i := rfl

end Bai

end PiIrrationality.BaiPF
end

-- ===== inlined: scratch.research.campaign_pick.pi_stage2.PolyInt =====
section
set_option autoImplicit false

/-!
# Generic infrastructure for the polynomial-part integrality (Bai Lemma 2.5 analogue)

* `ant S`: the antiderivative of a complex polynomial, `Lam S z0 z1 = ∫_{z0}^{z1} S` (algebraically,
  `ant S (z1) - ant S (z0)`), with linearity, the change of variables `Lam_comp`, the Taylor form and
  the coefficient-sum form.
* `TI e z`: the Gaussian number `z` lies in `2^e ℤ_(2)[i]`, i.e. `d z = 2^e (x + y i)` for an odd `d`.
  Closed under `+`, `*`, powers, finite sums; `PTI p` says all coefficients of `p` are `TI 0`.
-/

namespace PiIrrationality.PolyInt

open Polynomial Complex

/-! ## Antiderivatives -/

/-- The antiderivative of `S` with zero constant term. -/
noncomputable def ant (S : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ Finset.range (S.natDegree + 1), monomial (k + 1) (S.coeff k / (k + 1))

theorem coeff_ant_succ (S : ℂ[X]) (n : ℕ) : (ant S).coeff (n + 1) = S.coeff n / (n + 1) := by
  simp only [ant, finsetSum_coeff, coeff_monomial, add_left_inj, Finset.sum_ite_eq',
    Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_div]

theorem derivative_ant (S : ℂ[X]) : derivative (ant S) = S := by
  ext n
  rw [coeff_derivative, coeff_ant_succ]
  have : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  exact div_mul_cancel₀ _ this

theorem eval_sub_eq_of_derivative_eq {F G : ℂ[X]} (h : derivative F = derivative G) (z0 z1 : ℂ) :
    F.eval z1 - F.eval z0 = G.eval z1 - G.eval z0 := by
  have h0 : derivative (F - G) = 0 := by rw [derivative_sub, h, sub_self]
  rw [derivative_eq_zero] at h0
  have hc := eq_C_of_natDegree_eq_zero h0
  have e1 : (F - G).eval z1 = (F - G).eval z0 := by rw [hc]; simp
  simp only [eval_sub] at e1
  linear_combination e1

/-- `Lam S z0 z1 = ∫_{z0}^{z1} S(t) dt` for a polynomial `S`. -/
noncomputable def Lam (S : ℂ[X]) (z0 z1 : ℂ) : ℂ := (ant S).eval z1 - (ant S).eval z0

theorem Lam_of_derivative {F S : ℂ[X]} (h : derivative F = S) (z0 z1 : ℂ) :
    Lam S z0 z1 = F.eval z1 - F.eval z0 :=
  eval_sub_eq_of_derivative_eq (by rw [derivative_ant, h]) z0 z1

theorem Lam_add (S S' : ℂ[X]) (z0 z1 : ℂ) : Lam (S + S') z0 z1 = Lam S z0 z1 + Lam S' z0 z1 := by
  rw [Lam_of_derivative (F := ant S + ant S') (by rw [derivative_add, derivative_ant,
    derivative_ant])]
  simp only [Lam, eval_add]; ring

theorem Lam_C_mul (c : ℂ) (S : ℂ[X]) (z0 z1 : ℂ) : Lam (C c * S) z0 z1 = c * Lam S z0 z1 := by
  rw [Lam_of_derivative (F := C c * ant S) (by rw [derivative_C_mul, derivative_ant])]
  simp only [Lam, eval_mul, eval_C]; ring

theorem Lam_comp (S : ℂ[X]) (α β z0 z1 : ℂ) (hα : α ≠ 0) :
    Lam (S.comp (C α * X + C β)) z0 z1 = α⁻¹ * Lam S (α * z0 + β) (α * z1 + β) := by
  rw [Lam_of_derivative (F := C α⁻¹ * (ant S).comp (C α * X + C β))]
  · simp only [Lam, eval_mul, eval_C, eval_comp, eval_add, eval_X]; ring
  · rw [derivative_C_mul, derivative_comp, derivative_ant]
    simp only [derivative_add, derivative_C_mul, derivative_X, derivative_C, mul_one, add_zero]
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hα, C_1, one_mul]

/-- The Taylor form: `∫_{z0}^{z1} S = ∫_0^{z1-z0} S(z0 + x) dx`. -/
theorem Lam_taylor (S : ℂ[X]) (z0 z1 : ℂ) :
    Lam S z0 z1 = Lam (S.comp (X + C z0)) 0 (z1 - z0) := by
  have h := Lam_comp S 1 z0 0 (z1 - z0) one_ne_zero
  rw [C_1, one_mul] at h
  rw [h]; simp

theorem Lam_eq_sum (S : ℂ[X]) (z0 z1 : ℂ) (M : ℕ) (hM : S.natDegree < M) :
    Lam S z0 z1 = ∑ k ∈ Finset.range M, S.coeff k * ((z1 ^ (k + 1) - z0 ^ (k + 1)) / (k + 1)) := by
  have key : ∀ z, (ant S).eval z =
      ∑ k ∈ Finset.range (S.natDegree + 1), S.coeff k / (k + 1) * z ^ (k + 1) := by
    intro z; simp [ant, eval_finsetSum, eval_monomial]
  rw [Lam, key, key, ← Finset.sum_sub_distrib]
  calc ∑ k ∈ Finset.range (S.natDegree + 1),
        (S.coeff k / (k + 1) * z1 ^ (k + 1) - S.coeff k / (k + 1) * z0 ^ (k + 1))
      = ∑ k ∈ Finset.range (S.natDegree + 1),
          S.coeff k * ((z1 ^ (k + 1) - z0 ^ (k + 1)) / (k + 1)) := by
        apply Finset.sum_congr rfl; intro k _; ring
    _ = _ := by
        apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
        intro k _ hk
        rw [Finset.mem_range, not_lt] at hk
        rw [coeff_eq_zero_of_natDegree_lt (by omega)]; ring

/-! ## `I (α^m - γ^m)` is an integer for conjugate Gaussian integers -/

theorem I_mul_pow_sub_int (α γ : ℂ) (A B c : ℤ) (hs : α + γ = A) (hp : α * γ = B)
    (hd : α - γ = I * c) (m : ℕ) : ∃ z : ℤ, I * (α ^ m - γ ^ m) = z := by
  have key : ∀ m : ℕ, (∃ z : ℤ, I * (α ^ m - γ ^ m) = z) ∧
      (∃ z : ℤ, I * (α ^ (m + 1) - γ ^ (m + 1)) = z) := by
    intro m
    induction m with
    | zero =>
      refine ⟨⟨0, by simp⟩, ⟨-c, ?_⟩⟩
      simp only [zero_add, pow_one, hd]
      push_cast
      linear_combination (c : ℂ) * I_mul_I
    | succ m ih =>
      obtain ⟨⟨z0, h0⟩, ⟨z1, h1⟩⟩ := ih
      refine ⟨⟨z1, h1⟩, ⟨A * z1 - B * z0, ?_⟩⟩
      have hrec : α ^ (m + 1 + 1) - γ ^ (m + 1 + 1) =
          (α + γ) * (α ^ (m + 1) - γ ^ (m + 1)) - (α * γ) * (α ^ m - γ ^ m) := by ring
      rw [hrec, hs, hp]
      push_cast
      linear_combination (A : ℂ) * h1 - (B : ℂ) * h0
  exact (key m).1

/-! ## 2-adic Gaussian integrality -/

/-- `TI e z`: `d z = 2^e (x + y i)` for some odd `d` and integers `x, y`. -/
def TI (e : ℤ) (z : ℂ) : Prop :=
  ∃ d : ℕ, Odd d ∧ ∃ x y : ℤ, (d : ℂ) * z = (2 : ℂ) ^ e * (x + y * I)

theorem TI_zero (e : ℤ) : TI e 0 := ⟨1, odd_one, 0, 0, by simp⟩

theorem TI_add {e : ℤ} {z w : ℂ} (hz : TI e z) (hw : TI e w) : TI e (z + w) := by
  obtain ⟨d, hd, x, y, h⟩ := hz
  obtain ⟨d', hd', x', y', h'⟩ := hw
  refine ⟨d * d', hd.mul hd', d' * x + d * x', d' * y + d * y', ?_⟩
  push_cast
  linear_combination (d' : ℂ) * h + (d : ℂ) * h'

theorem TI_neg {e : ℤ} {z : ℂ} (hz : TI e z) : TI e (-z) := by
  obtain ⟨d, hd, x, y, h⟩ := hz
  refine ⟨d, hd, -x, -y, ?_⟩
  push_cast
  linear_combination -h

theorem TI_sub {e : ℤ} {z w : ℂ} (hz : TI e z) (hw : TI e w) : TI e (z - w) := by
  rw [sub_eq_add_neg]; exact TI_add hz (TI_neg hw)

theorem TI_mul {e f : ℤ} {z w : ℂ} (hz : TI e z) (hw : TI f w) : TI (e + f) (z * w) := by
  obtain ⟨d, hd, x, y, h⟩ := hz
  obtain ⟨d', hd', x', y', h'⟩ := hw
  refine ⟨d * d', hd.mul hd', x * x' - y * y', x * y' + y * x', ?_⟩
  rw [zpow_add₀ two_ne_zero]
  push_cast
  calc (d : ℂ) * d' * (z * w) = ((d : ℂ) * z) * ((d' : ℂ) * w) := by ring
    _ = _ := by
      rw [h, h']
      linear_combination (2 : ℂ) ^ e * 2 ^ f * (y : ℂ) * y' * I_mul_I

theorem TI_mono {e f : ℤ} (hfe : f ≤ e) {z : ℂ} (hz : TI e z) : TI f z := by
  obtain ⟨d, hd, x, y, h⟩ := hz
  obtain ⟨m, hm⟩ : ∃ m : ℕ, e = f + m := ⟨(e - f).toNat, by omega⟩
  refine ⟨d, hd, 2 ^ m * x, 2 ^ m * y, ?_⟩
  rw [h, hm, zpow_add₀ two_ne_zero, zpow_natCast]; push_cast; ring

theorem TI_congr {e f : ℤ} (hef : e = f) {z : ℂ} (hz : TI e z) : TI f z := hef ▸ hz

theorem TI_int (x : ℤ) : TI 0 (x : ℂ) := ⟨1, odd_one, x, 0, by simp⟩

theorem TI_nat (x : ℕ) : TI 0 (x : ℂ) := by
  have := TI_int x; simpa using this

theorem TI_of_dvd (x : ℤ) (e : ℕ) (h : (2 : ℤ) ^ e ∣ x) : TI e (x : ℂ) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨1, odd_one, m, 0, ?_⟩
  rw [hm, zpow_natCast]; push_cast; ring

theorem TI_two_zpow (e : ℤ) : TI e ((2 : ℂ) ^ e) := ⟨1, odd_one, 1, 0, by simp⟩

theorem TI_inv_odd (d : ℕ) (hd : Odd d) : TI 0 ((d : ℂ)⁻¹) := by
  have hd0 : (d : ℂ) ≠ 0 := by
    have : d ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hd)
    exact_mod_cast this
  exact ⟨d, hd, 1, 0, by field_simp; simp⟩

theorem TI_I : TI 0 I := ⟨1, odd_one, 0, 1, by simp⟩

theorem TI_pow {e : ℤ} {z : ℂ} (hz : TI e z) (m : ℕ) : TI (m * e) (z ^ m) := by
  induction m with
  | zero => simpa using TI_int 1
  | succ m ih =>
    rw [pow_succ]
    exact TI_congr (by push_cast; ring) (TI_mul ih hz)

theorem TI_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) (e : ℤ) (h : ∀ i ∈ s, TI e (f i)) :
    TI e (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using TI_zero e
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact TI_add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- A rational number that is `TI 0` has an odd denominator. -/
theorem TI_rat (q : ℚ) (h : TI 0 (q : ℂ)) : ∃ d : ℕ, Odd d ∧ ∃ x : ℤ, (d : ℚ) * q = x := by
  obtain ⟨d, hd, x, y, hxy⟩ := h
  refine ⟨d, hd, x, ?_⟩
  have := congrArg Complex.re hxy
  simp at this
  exact_mod_cast this

theorem TI_two_add_I_pow (m : ℕ) : TI 0 ((2 + I) ^ m) := by
  have h : TI 0 (2 + I) := ⟨1, odd_one, 2, 1, by simp⟩
  simpa using TI_pow h m

theorem TI_two_sub_I_div_five : TI 0 ((2 - I) / 5) :=
  ⟨5, by decide, 2, -1, by push_cast; ring⟩

/-- `((3-i)/2)^m ∈ 2^{-⌈m/2⌉} ℤ_(2)[i]`, from `(3-i)^2 = 2(4-3i)`. -/
theorem TI_three_sub_I_half_pow (m : ℕ) :
    TI (-(((m + 1) / 2 : ℕ) : ℤ)) (((3 - I) / 2) ^ m) := by
  have hsq : ((3 - I) / 2) ^ 2 = (4 - 3 * I) / 2 := by
    linear_combination (1 / 4 : ℂ) * I_mul_I
  have h43 : TI (-1) ((4 - 3 * I) / 2) :=
    ⟨1, odd_one, 4, -3, by rw [zpow_neg_one]; push_cast; ring⟩
  have h3 : TI (-1) ((3 - I) / 2) :=
    ⟨1, odd_one, 3, -1, by rw [zpow_neg_one]; push_cast; ring⟩
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · rw [pow_mul, hsq]
    exact TI_congr (by push_cast; omega) (TI_pow h43 j)
  · rw [pow_succ, pow_mul, hsq]
    exact TI_congr (by push_cast; omega) (TI_mul (TI_pow h43 j) h3)

/-! ## Polynomials with `TI 0` coefficients -/

/-- All coefficients are `TI 0`. -/
def PTI (p : ℂ[X]) : Prop := ∀ k, TI 0 (p.coeff k)

theorem PTI_add {p q : ℂ[X]} (hp : PTI p) (hq : PTI q) : PTI (p + q) := by
  intro k; rw [coeff_add]; exact TI_add (hp k) (hq k)

theorem PTI_mul {p q : ℂ[X]} (hp : PTI p) (hq : PTI q) : PTI (p * q) := by
  intro k; rw [coeff_mul]
  exact TI_sum _ _ 0 (fun x _ => TI_congr (by simp) (TI_mul (hp x.1) (hq x.2)))

theorem PTI_C {z : ℂ} (hz : TI 0 z) : PTI (C z) := by
  intro k; rw [coeff_C]; split_ifs
  · exact hz
  · exact TI_zero 0

theorem PTI_X : PTI (X : ℂ[X]) := by
  intro k; rw [coeff_X]; split_ifs
  · simpa using TI_int 1
  · exact TI_zero 0

theorem PTI_pow {p : ℂ[X]} (hp : PTI p) (m : ℕ) : PTI (p ^ m) := by
  induction m with
  | zero => simpa using PTI_C (TI_int 1)
  | succ m ih => rw [pow_succ]; exact PTI_mul ih hp

theorem PTI_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) (h : ∀ i ∈ s, PTI (f i)) :
    PTI (∑ i ∈ s, f i) := by
  intro k; rw [finsetSum_coeff]; exact TI_sum _ _ 0 (fun i hi => h i hi k)

theorem PTI_comp {p q : ℂ[X]} (hp : PTI p) (hq : PTI q) : PTI (p.comp q) := by
  rw [comp_eq_sum_left, Polynomial.sum_def]
  exact PTI_sum _ _ (fun n _ => PTI_mul (PTI_C (hp n)) (PTI_pow hq n))

theorem PTI_map_int (p : ℤ[X]) : PTI (p.map (Int.castRingHom ℂ)) := by
  intro k; rw [coeff_map]; exact TI_int _

end PiIrrationality.PolyInt
end

-- ===== inlined: scratch.research.campaign_pick.pi_stage2.TwoAdic =====
section
set_option autoImplicit false

/-!
# The 2-adic size of `g_{n,i}` (the 2-adic part of Bai's Lemma 2.1)

`Q(w) = 2(1 - 7w) + w²(39 - 50w + 25w²)`, so every coefficient of `Q^{bn}` at `w^i` is divisible by
`2^{bn - ⌊i/2⌋}`, and the same holds for `g_{n,i} = [w^i] (2w-1)^{2an} Q^{bn} (1-w)^{-(cn+1)}`.
-/

namespace PiIrrationality.BaiTwo

open Polynomial PiIrrationality.BaiGen

/-- `TwoW e f`: `2^{e - ⌊i/2⌋} ∣ [w^i] f` for every `i`. -/
def TwoW (e : ℕ) (f : PowerSeries ℤ) : Prop :=
  ∀ i, (2 : ℤ) ^ (e - i / 2) ∣ PowerSeries.coeff i f

theorem TwoW_mul {e e' : ℕ} {f f' : PowerSeries ℤ} (hf : TwoW e f) (hf' : TwoW e' f') :
    TwoW (e + e') (f * f') := by
  intro i
  rw [PowerSeries.coeff_mul]
  apply Finset.dvd_sum
  intro x hx
  have hx' : x.1 + x.2 = i := Finset.mem_antidiagonal.1 hx
  have hle : e + e' - i / 2 ≤ (e - x.1 / 2) + (e' - x.2 / 2) := by omega
  exact (pow_dvd_pow 2 hle).trans (by rw [pow_add]; exact mul_dvd_mul (hf x.1) (hf' x.2))

theorem TwoW_zero (f : PowerSeries ℤ) : TwoW 0 f := by
  intro i; simp

theorem TwoW_pow {e : ℕ} {f : PowerSeries ℤ} (hf : TwoW e f) (m : ℕ) : TwoW (m * e) (f ^ m) := by
  induction m with
  | zero => simpa using TwoW_zero 1
  | succ m ih => rw [pow_succ, Nat.succ_mul]; exact TwoW_mul ih hf

theorem TwoW_Qw : TwoW 1 (Qw : PowerSeries ℤ) := by
  intro i
  rw [Polynomial.coeff_coe]
  rcases i with _ | _ | i
  · norm_num [Qw, coeff_X, coeff_one, coeff_X_pow]
  · norm_num [Qw, coeff_X, coeff_one, coeff_X_pow]
  · rw [show 1 - (i + 1 + 1) / 2 = 0 by omega, pow_zero]
    exact one_dvd _

/-- `2^{bn - ⌊i/2⌋} ∣ g_{n,i}`. -/
theorem g_two_adic (a b c n i : ℕ) : (2 : ℤ) ^ (b * n - i / 2) ∣ g a b c n i := by
  have h : TwoW (0 + b * n * 1 + 0) (Gw a b c n) := by
    unfold Gw Hw
    rw [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_pow]
    exact TwoW_mul (TwoW_mul (TwoW_zero _) (TwoW_pow TwoW_Qw (b * n))) (TwoW_zero _)
  simpa [g] using h i

end PiIrrationality.BaiTwo
end

-- ===== inlined: scratch.research.campaign_pick.pi_stage2.Taylor =====
section
set_option autoImplicit false

/-!
# Taylor coefficients of the polynomial part at the endpoint (Bai's Lemma 2.4, in `w`)

`w₀ = (2-i)/5` is the image of `t₀ = -1-2i`; `1/w₀ = 2+i` and `1/(1-w₀) = (3-i)/2`.
With `β_k = [x^k] Q(w₀ + x)` (Taylor coefficients of the polynomial part `Q = Qp H N`), the
partial-fraction identity divided by `(w₀+x)^{N+1} (1-w₀-x)^{N+1}` in `ℂ[[x]]` gives, for `k < s`
when `x^s ∣ H(w₀ + x)`,
`β_k = -Σ_{i ≤ N} g_i C(N-i+k, N-i) ((2+i)^{N-i+1} (-(2+i))^k + ((3-i)/2)^{N-i+1} ((3-i)/2)^k)`.
At Bai's numerator `x^{bn} ∣ H_n(w₀+x)` (since `Q(w₀) = 0`), and with `2^{bn-⌊i/2⌋} ∣ g_i`
this gives `β_k ∈ 2^{bn - cn/2 - (k+1)} ℤ_(2)[i]` for every `k` (`beta_TI`).
-/

namespace PiIrrationality.BaiTaylor

open Polynomial Complex PiIrrationality.BaiPF PiIrrationality.PolyInt

/-- `w₀ = (2-i)/5`, the image of the endpoint `t₀ = -1-2i` under `w = (t+5)/10`. -/
noncomputable def w0 : ℂ := (2 - I) / 5

theorem w0_mul : w0 * (2 + I) = 1 := by unfold w0; linear_combination (-1 / 5 : ℂ) * I_sq

theorem one_sub_w0_mul : (1 - w0) * ((3 - I) / 2) = 1 := by
  unfold w0; linear_combination (-1 / 10 : ℂ) * I_sq

theorem w0_ne : w0 ≠ 0 := left_ne_zero_of_mul_eq_one w0_mul

theorem one_sub_w0_ne : 1 - w0 ≠ 0 := left_ne_zero_of_mul_eq_one one_sub_w0_mul

theorem w0_inv : w0⁻¹ = 2 + I := inv_eq_of_mul_eq_one_right w0_mul

theorem one_sub_w0_inv : (1 - w0)⁻¹ = (3 - I) / 2 := inv_eq_of_mul_eq_one_right one_sub_w0_mul

/-! ## Inverses of linear power series -/

/-- `α (1 - ρ x)`. -/
noncomputable def Lin (α ρ : ℂ) : PowerSeries ℂ :=
  PowerSeries.C α * (1 - PowerSeries.C ρ * PowerSeries.X)

/-- `(α (1 - ρ x))^{-m} = α^{-m} Σ_k C(m-1+k, k) ρ^k x^k`. -/
noncomputable def GInv (α ρ : ℂ) (m : ℕ) : PowerSeries ℂ :=
  PowerSeries.C (α⁻¹ ^ m) * PowerSeries.rescale ρ (PowerSeries.invOneSubPow ℂ m).val

theorem Lin_pow_mul_GInv (α ρ : ℂ) (hα : α ≠ 0) (m : ℕ) : Lin α ρ ^ m * GInv α ρ m = 1 := by
  have h1 : (1 - PowerSeries.C ρ * PowerSeries.X : PowerSeries ℂ) =
      PowerSeries.rescale ρ (1 - PowerSeries.X) := by
    rw [map_sub, map_one, PowerSeries.rescale_X]
  have h2 : (1 - PowerSeries.X : PowerSeries ℂ) ^ m * (PowerSeries.invOneSubPow ℂ m).val = 1 := by
    rw [← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
    exact (PowerSeries.invOneSubPow ℂ m).inv_val
  unfold Lin GInv
  rw [h1]
  have : (PowerSeries.C α * PowerSeries.rescale ρ (1 - PowerSeries.X)) ^ m *
      (PowerSeries.C (α⁻¹ ^ m) * PowerSeries.rescale ρ (PowerSeries.invOneSubPow ℂ m).val) =
      PowerSeries.C ((α * α⁻¹) ^ m) *
        PowerSeries.rescale ρ ((1 - PowerSeries.X) ^ m * (PowerSeries.invOneSubPow ℂ m).val) := by
    simp only [map_mul, map_pow, mul_pow]; ring
  rw [this, h2, map_one, mul_inv_cancel₀ hα, one_pow, map_one, one_mul]

theorem coeff_GInv_succ (α ρ : ℂ) (m k : ℕ) :
    PowerSeries.coeff k (GInv α ρ (m + 1)) = α⁻¹ ^ (m + 1) * ρ ^ k * ((m + k).choose m : ℂ) := by
  rw [GInv, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk]
  ring

theorem GInv_add (α ρ : ℂ) (i m : ℕ) : GInv α ρ (i + m) = GInv α ρ i * GInv α ρ m := by
  unfold GInv
  rw [PowerSeries.invOneSubPow_add, Units.val_mul, map_mul, pow_add, map_mul]
  ring

theorem Lin_pow_mul_GInv_add (α ρ : ℂ) (hα : α ≠ 0) (i m : ℕ) :
    Lin α ρ ^ i * GInv α ρ (i + m) = GInv α ρ m := by
  rw [GInv_add, ← mul_assoc, Lin_pow_mul_GInv α ρ hα, one_mul]

/-! ## The shift `w = w₀ + x` -/

/-- `p ↦ p(w₀ + x) ∈ ℂ[[x]]`. -/
noncomputable def phi : ℤ[X] →+* PowerSeries ℂ :=
  (Polynomial.coeToPowerSeries.ringHom).comp
    ((Polynomial.compRingHom (X + C w0)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ)))

theorem phi_apply (p : ℤ[X]) :
    phi p = (((p.map (Int.castRingHom ℂ)).comp (X + C w0) : ℂ[X]) : PowerSeries ℂ) := rfl

theorem phi_X : phi X = Lin w0 (-w0⁻¹) := by
  rw [phi_apply, Polynomial.map_X, X_comp, Polynomial.coe_add, Polynomial.coe_X,
    Polynomial.coe_C]
  unfold Lin
  rw [mul_sub, mul_one, ← mul_assoc, ← map_mul, mul_neg, mul_inv_cancel₀ w0_ne, map_neg, map_one]
  ring

theorem phi_one_sub_X : phi (1 - X) = Lin (1 - w0) ((1 - w0)⁻¹) := by
  rw [map_sub, map_one, phi_X]
  unfold Lin
  rw [mul_sub, mul_sub, mul_one, mul_one, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_neg,
    mul_inv_cancel₀ w0_ne, mul_inv_cancel₀ one_sub_w0_ne, map_neg, map_one, map_sub, map_one]
  ring

theorem phi_C (z : ℤ) : phi (C z) = PowerSeries.C (z : ℂ) := by
  rw [phi_apply, Polynomial.map_C, C_comp, Polynomial.coe_C]
  simp

/-- The Taylor coefficients `β_k = [x^k] Q(w₀ + x)` of the polynomial part. -/
noncomputable def beta (H : ℤ[X]) (N k : ℕ) : ℂ :=
  (((Qp H N).map (Int.castRingHom ℂ)).comp (X + C w0)).coeff k

/-- The Taylor-coefficient formula below the vanishing order `s` of `H` at `w₀`. -/
theorem beta_formula (H : ℤ[X]) (N s : ℕ) (hsym : H.comp (1 - X) = H)
    (hs : (X : ℂ[X]) ^ s ∣ (H.map (Int.castRingHom ℂ)).comp (X + C w0)) (k : ℕ) (hk : k < s) :
    beta H N k = -∑ i ∈ Finset.range (N + 1), (gc H N i : ℂ) * ((N - i + k).choose (N - i) : ℂ) *
      ((2 + I) ^ (N - i + 1) * (-(2 + I)) ^ k + ((3 - I) / 2) ^ (N - i + 1) * ((3 - I) / 2) ^ k) := by
  set A := Lin w0 (-w0⁻¹) with hA
  set B := Lin (1 - w0) ((1 - w0)⁻¹) with hB
  set Ai := GInv w0 (-w0⁻¹) (N + 1) with hAi
  set Bi := GInv (1 - w0) ((1 - w0)⁻¹) (N + 1) with hBi
  set SA := ∑ i ∈ Finset.range (N + 1), PowerSeries.C (gc H N i : ℂ) * A ^ i with hSA
  set SB := ∑ i ∈ Finset.range (N + 1), PowerSeries.C (gc H N i : ℂ) * B ^ i with hSB
  have hT : phi (T H N) = SA := by
    rw [T, map_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [map_mul, map_pow, phi_C, phi_X]
  have hT1 : phi ((T H N).comp (1 - X)) = SB := by
    rw [T_comp_one_sub, map_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [map_mul, map_pow, phi_C, phi_one_sub_X]
  have hpf := congrArg phi (pf_identity H N hsym)
  rw [Rem, map_add, map_add, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_mul,
    phi_X, phi_one_sub_X, hT, hT1] at hpf
  have eA : A ^ (N + 1) * Ai = 1 := Lin_pow_mul_GInv _ _ w0_ne _
  have eB : B ^ (N + 1) * Bi = 1 := Lin_pow_mul_GInv _ _ one_sub_w0_ne _
  have key : phi (Qp H N) = phi H * Ai * Bi - SA * Ai - SB * Bi := by
    rw [hpf]
    linear_combination (-phi (Qp H N) - SB * Bi) * eA +
      (-phi (Qp H N) * (A ^ (N + 1) * Ai) - SA * Ai) * eB
  -- the first term vanishes below order `s`
  obtain ⟨R, hR⟩ := hs
  have hH : phi H = PowerSeries.X ^ s * (R : PowerSeries ℂ) := by
    rw [phi_apply, hR, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X]
  have hc := congrArg (PowerSeries.coeff k) key
  rw [hH, map_sub, map_sub, show PowerSeries.X ^ s * (R : PowerSeries ℂ) * Ai * Bi =
      PowerSeries.X ^ s * ((R : PowerSeries ℂ) * Ai * Bi) by ring,
    PowerSeries.coeff_X_pow_mul', if_neg (show ¬ s ≤ k by omega), zero_sub] at hc
  -- the pole terms
  have hSA' : SA * Ai = ∑ i ∈ Finset.range (N + 1),
      PowerSeries.C (gc H N i : ℂ) * GInv w0 (-w0⁻¹) (N - i + 1) := by
    rw [hSA, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i hi
    rw [Finset.mem_range] at hi
    rw [mul_assoc, hAi, show N + 1 = i + (N - i + 1) by omega,
      Lin_pow_mul_GInv_add _ _ w0_ne]
  have hSB' : SB * Bi = ∑ i ∈ Finset.range (N + 1),
      PowerSeries.C (gc H N i : ℂ) * GInv (1 - w0) ((1 - w0)⁻¹) (N - i + 1) := by
    rw [hSB, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i hi
    rw [Finset.mem_range] at hi
    rw [mul_assoc, hBi, show N + 1 = i + (N - i + 1) by omega,
      Lin_pow_mul_GInv_add _ _ one_sub_w0_ne]
  rw [hSA', hSB', map_sum, map_sum] at hc
  have hsum : ∑ i ∈ Finset.range (N + 1), PowerSeries.coeff k
        (PowerSeries.C (gc H N i : ℂ) * GInv w0 (-w0⁻¹) (N - i + 1)) +
      ∑ i ∈ Finset.range (N + 1), PowerSeries.coeff k
        (PowerSeries.C (gc H N i : ℂ) * GInv (1 - w0) ((1 - w0)⁻¹) (N - i + 1)) =
      ∑ i ∈ Finset.range (N + 1), (gc H N i : ℂ) * ((N - i + k).choose (N - i) : ℂ) *
        ((2 + I) ^ (N - i + 1) * (-(2 + I)) ^ k + ((3 - I) / 2) ^ (N - i + 1) * ((3 - I) / 2) ^ k) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, coeff_GInv_succ, coeff_GInv_succ, w0_inv,
      one_sub_w0_inv]
    ring
  rw [beta, ← Polynomial.coeff_coe, ← phi_apply, hc, ← hsum]
  ring

/-! ## Bai's numerator vanishes to order `bn` at `w₀` -/

open PiIrrationality.BaiGen in
theorem X_pow_dvd_Hw (a b n : ℕ) :
    (X : ℂ[X]) ^ (b * n) ∣ ((Hw a b n).map (Int.castRingHom ℂ)).comp (X + C w0) := by
  have hq : (X : ℂ[X]) ∣ ((Qw).map (Int.castRingHom ℂ)).comp (X + C w0) := by
    rw [X_dvd_iff, coeff_zero_eq_eval_zero, eval_comp]
    have h0 : (X + C w0 : ℂ[X]).eval 0 = w0 := by simp
    have hw : 5 * w0 ^ 2 - 4 * w0 + 1 = 0 := by unfold w0; linear_combination (1 / 5 : ℂ) * I_sq
    rw [h0]
    simp [Qw]
    linear_combination (5 * w0 ^ 2 - 6 * w0 + 2) * hw
  unfold Hw
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, mul_comp, pow_comp, pow_comp]
  exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hq _) _

/-! ## The 2-adic bound on `β_k` -/

theorem TI_neg_two_add_I_pow (k : ℕ) : TI 0 ((-(2 + I)) ^ k) := by
  have h : TI 0 (-(2 + I)) := ⟨1, odd_one, -2, -1, by push_cast; ring⟩
  simpa using TI_pow h k

theorem beta_PTI (H : ℤ[X]) (N k : ℕ) : TI 0 (beta H N k) :=
  PTI_comp (PTI_map_int _) (PTI_add PTI_X (PTI_C TI_two_sub_I_div_five)) k

open PiIrrationality.BaiGen in
/-- `β_k ∈ 2^{bn - cn/2 - (k+1)} ℤ_(2)[i]` (Bai's Lemma 2.4 in the variable `w`). -/
theorem beta_TI (a b c n k : ℕ) (hc : Even (c * n)) :
    TI ((b * n : ℕ) - ((c * n / 2 : ℕ) : ℤ) - (k + 1)) (beta (Hw a b n) (c * n) k) := by
  obtain ⟨r, hr⟩ := hc
  by_cases hk : k < b * n
  · rw [beta_formula (Hw a b n) (c * n) (b * n) (BaiPF.Hw_comp a b n) (X_pow_dvd_Hw a b n) k hk]
    apply TI_neg
    apply TI_sum
    intro i hi
    rw [Finset.mem_range] at hi
    have hg : TI ((b * n - i / 2 : ℕ) : ℤ) (gc (Hw a b n) (c * n) i : ℂ) := by
      rw [gc_eq]; exact TI_of_dvd _ _ (BaiTwo.g_two_adic a b c n i)
    have hC : TI 0 (((c * n - i + k).choose (c * n - i) : ℕ) : ℂ) := TI_nat _
    rw [mul_add]
    apply TI_add
    · have h1 := TI_mul (TI_mul hg hC)
        (TI_mul (TI_two_add_I_pow (c * n - i + 1)) (TI_neg_two_add_I_pow k))
      refine TI_mono ?_ h1
      omega
    · rw [← pow_add]
      have h2 := TI_mul (TI_mul hg hC) (TI_three_sub_I_half_pow (c * n - i + 1 + k))
      refine TI_mono ?_ h2
      omega
  · exact TI_mono (by omega) (beta_PTI _ _ k)

end PiIrrationality.BaiTaylor
end

-- ===== inlined: scratch.research.campaign_pick.pi_stage2.TVar =====
section
set_option autoImplicit false

/-!
# Bai's polynomial part `P_n(t)` and its relation to the `w`-picture

`P_n(t)` is the polynomial part of `R_n(t) = N_n(t)/(25-t²)^{cn+1}`,
`N_n(t) = 5 t^{2an} (t⁴+6t²+25)^{bn}`, defined by division by the monic `(t²-25)^{cn+1}`; it has
integer coefficients. Uniqueness of division gives `P_n(t) = K_n Q((t+5)/10)` with
`K_n = 5^{2an+1} 400^{bn} / 100^{cn+1}` and `Q = Qp H_n (cn)` the polynomial part in `w`, so
`∫_{t₀}^{t₁} P_n = 10 K_n ∫_{w₀}^{w̄₀} Q` with `t₀ = -1-2i`, `t₁ = -1+2i`, `w₀ = (2-i)/5`, `w̄₀ = (2+i)/5`.
-/

namespace PiIrrationality.BaiGen

open Polynomial Complex PiIrrationality.BaiPF PiIrrationality.PolyInt

variable (a b c : ℕ)

/-- `N_n(t) = 5 t^{2an} (t⁴ + 6t² + 25)^{bn}`. -/
noncomputable def Nt (n : ℕ) : ℤ[X] := 5 * X ^ (2 * a * n) * (X ^ 4 + 6 * X ^ 2 + 25) ^ (b * n)

/-- `(t² - 25)^{cn+1}`, monic. -/
noncomputable def Dt (n : ℕ) : ℤ[X] := (X ^ 2 - C 25) ^ (c * n + 1)

/-- Bai's polynomial part `P_n(t)` of `R_n(t) = N_n(t) / (25 - t²)^{cn+1}`. -/
noncomputable def Pt (n : ℕ) : ℤ[X] := (-1) ^ (c * n + 1) * (Nt a b n /ₘ Dt c n)

/-- `K_n = 5^{2an+1} 400^{bn} / 100^{cn+1}`. -/
noncomputable def Kc (n : ℕ) : ℂ := 5 ^ (2 * a * n + 1) * 400 ^ (b * n) / 100 ^ (c * n + 1)

/-- `w = t/10 + 1/2`. -/
noncomputable def sigt : ℂ[X] := C (1 / 10 : ℂ) * X + C (1 / 2)

theorem Dt_monic (n : ℕ) : (Dt c n).Monic := (monic_X_pow_sub_C 25 two_ne_zero).pow _

theorem natDegree_Dt (n : ℕ) : (Dt c n).natDegree = 2 * (c * n + 1) := by
  rw [Dt, (monic_X_pow_sub_C (25 : ℤ) two_ne_zero).natDegree_pow, natDegree_X_pow_sub_C]; ring

theorem natDegree_Nt_le (n : ℕ) : (Nt a b n).natDegree ≤ 2 * a * n + 4 * (b * n) := by
  unfold Nt
  have h1 : ((X : ℤ[X]) ^ 4 + 6 * X ^ 2 + 25).natDegree ≤ 4 := by compute_degree!
  refine (natDegree_mul_le).trans (add_le_add ((natDegree_mul_le).trans ?_) ?_)
  · have : ((5 : ℤ[X])).natDegree = 0 := natDegree_ofNat 5
    rw [this, natDegree_X_pow]; omega
  · refine (natDegree_pow_le).trans ?_
    have := Nat.mul_le_mul_left (b * n) h1
    linarith

theorem natDegree_Pt_le (n : ℕ) :
    (Pt a b c n).natDegree ≤ 2 * a * n + 4 * (b * n) - 2 * (c * n + 1) := by
  unfold Pt
  refine (natDegree_mul_le).trans ?_
  have h1 : (((-1 : ℤ[X])) ^ (c * n + 1)).natDegree = 0 := by
    rw [← C_1, ← C_neg, ← C_pow, natDegree_C]
  rw [h1, zero_add, natDegree_divByMonic _ (Dt_monic c n), natDegree_Dt]
  have := natDegree_Nt_le a b n
  omega

/-- `P_n(t) = K_n Q(t/10 + 1/2)`. -/
theorem Pt_map (n : ℕ) : (Pt a b c n).map (Int.castRingHom ℂ) =
    C (Kc a b c n) * ((Qp (Hw a b n) (c * n)).map (Int.castRingHom ℂ)).comp sigt := by
  set N := c * n with hN
  set Qc := (Qp (Hw a b n) N).map (Int.castRingHom ℂ) with hQc
  set Rc := (Rem (Hw a b n) N).map (Int.castRingHom ℂ) with hRc
  set K := Kc a b c n with hK
  have hD : ((Dt c n).map (Int.castRingHom ℂ)).Monic := (Dt_monic c n).map _
  -- the partial-fraction identity at `w`
  have hpfw : ∀ w : ℂ, ((Hw a b n).map (Int.castRingHom ℂ)).eval w =
      (w * (1 - w)) ^ (N + 1) * Qc.eval w + Rc.eval w := by
    intro w
    have := congrArg (fun p : ℤ[X] => (p.map (Int.castRingHom ℂ)).eval w)
      (pf_identity (Hw a b n) N (Hw_comp a b n))
    simpa [hQc, hRc] using this
  have hHw : ∀ w : ℂ, ((Hw a b n).map (Int.castRingHom ℂ)).eval w =
      (2 * w - 1) ^ (2 * a * n) * (25 * w ^ 4 - 50 * w ^ 3 + 39 * w ^ 2 - 14 * w + 2) ^ (b * n) := by
    intro w; simp [Hw, Qw]
  have hNt : ∀ z : ℂ, ((Nt a b n).map (Int.castRingHom ℂ)).eval z =
      5 * z ^ (2 * a * n) * (z ^ 4 + 6 * z ^ 2 + 25) ^ (b * n) := by
    intro z; simp [Nt]
  have hDt : ∀ z : ℂ, ((Dt c n).map (Int.castRingHom ℂ)).eval z = (z ^ 2 - 25) ^ (N + 1) := by
    intro z; simp [Dt, hN]
  have heq : C (K * 100 ^ (N + 1)) * Rc.comp sigt +
      (Dt c n).map (Int.castRingHom ℂ) * ((-1) ^ (N + 1) * C K * Qc.comp sigt) =
      (Nt a b n).map (Int.castRingHom ℂ) := by
    apply Polynomial.funext
    intro z
    have hs : sigt.eval z = 1 / 10 * z + 1 / 2 := by simp [sigt]
    simp only [eval_add, eval_mul, eval_C, eval_comp, eval_pow, eval_neg, eval_one, hs, hDt, hNt]
    set w := 1 / 10 * z + 1 / 2 with hw
    have e1 : (z ^ 2 - 25) ^ (N + 1) * (-1) ^ (N + 1) = 100 ^ (N + 1) * (w * (1 - w)) ^ (N + 1) := by
      rw [← mul_pow, ← mul_pow]; congr 1; rw [hw]; ring
    have e2 : 5 * z ^ (2 * a * n) * (z ^ 4 + 6 * z ^ 2 + 25) ^ (b * n) =
        K * 100 ^ (N + 1) * ((Hw a b n).map (Int.castRingHom ℂ)).eval w := by
      rw [hHw]
      have h2w : 2 * w - 1 = z / 5 := by rw [hw]; ring
      have hq : 25 * w ^ 4 - 50 * w ^ 3 + 39 * w ^ 2 - 14 * w + 2 = (z ^ 4 + 6 * z ^ 2 + 25) / 400 := by
        rw [hw]; ring
      rw [h2w, hq, div_pow, div_pow, hK, Kc, ← hN]
      field_simp
      ring
    rw [e2, hpfw]
    linear_combination K * Qc.eval w * e1
  have hdeg : (C (K * 100 ^ (N + 1)) * Rc.comp sigt).degree <
      ((Dt c n).map (Int.castRingHom ℂ)).degree := by
    apply degree_lt_degree
    rw [(Dt_monic c n).natDegree_map, natDegree_Dt]
    refine (natDegree_C_mul_le _ _).trans_lt ?_
    refine (natDegree_comp_le).trans_lt ?_
    have h1 : Rc.natDegree ≤ 2 * N + 1 := (natDegree_map_le).trans (natDegree_Rem_le _ _)
    have h2 : sigt.natDegree ≤ 1 := natDegree_linear_le
    have := Nat.mul_le_mul h1 h2
    omega
  have huniq := div_modByMonic_unique _ _ hD ⟨heq, hdeg⟩
  rw [Pt, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_one,
    map_divByMonic _ (Dt_monic c n), huniq.1, ← mul_assoc, ← mul_assoc, ← mul_pow, neg_one_mul,
    neg_neg, one_pow, one_mul]

/-- `∫_{t₀}^{t₁} P_n = 10 K_n ∫_{w₀}^{w̄₀} Q`. -/
theorem Lam_Pt (n : ℕ) :
    Lam ((Pt a b c n).map (Int.castRingHom ℂ)) (-1 - 2 * I) (-1 + 2 * I) =
      10 * Kc a b c n * Lam ((Qp (Hw a b n) (c * n)).map (Int.castRingHom ℂ))
        ((2 - I) / 5) ((2 + I) / 5) := by
  rw [Pt_map, Lam_C_mul, sigt, Lam_comp _ _ _ _ _ (by norm_num : (1 / 10 : ℂ) ≠ 0),
    show (1 / 10 : ℂ) * (-1 - 2 * I) + 1 / 2 = (2 - I) / 5 by ring,
    show (1 / 10 : ℂ) * (-1 + 2 * I) + 1 / 2 = (2 + I) / 5 by ring]
  norm_num
  ring

end PiIrrationality.BaiGen
end

-- ===== inlined: scratch.research.campaign_pick.pi_stage2.Deletion =====
section
set_option autoImplicit false

/-!
# Bai Lemma 2.2 analogue: deleted-prime divisibility (stage 2, private)

For a deleted prime `p` (Bai (2.14): `{an/p + 1/2} + 2{bn/p} < {cn/p}`) and `p ∣ j`, the Laurent
coefficient `c_{j,n}` of `R_n` at `t = -5` is `≡ 0 (mod p)`; in particular `Φ_n ∣ c_{0,n}`.

Proof (in `𝔽_p[[w]]`, variable exponents throughout, nothing is expanded):
* `c_{j,n} = 2^{…} 5^{…} g_{n, cn-j}` with `g_{n,m} = [w^m] (2w-1)^{2an} Q(w)^{bn} (1-w)^{-(cn+1)}`
  (`BaiDefs.lean`), so it suffices that `[w^m] G_n ≡ 0` for `m ≡ cn (mod p)` (`ZR p (cn % p)`).
* Multiply by the unit `V = ((1-w)^{γ+1}(2w-1))^p`, a power series in `w^p` (`zr_cancel`). Then
  `V G_n = F(w)^p · (2w-1)^E Q(w)^{r_b} (1-w)^{p-1-r_c}` with `E = (p + 2an) mod 2p` odd.
* `p`-th powers only shift by multiples of `p` (`zr_mul`, `ps_coe_pow_p`).
* Core (`core_vanish`): `w^{p-1-r_c}(2w-1)^E Q^{r_b}(1-w)^{p-1-r_c} = (2w-1) K(w - w²)` with
  `deg K ≤ p - 2`, and `(2w-1)(w-w²)^k = -(k+1)⁻¹ d/dw (w-w²)^{k+1}`: a derivative has no monomials
  `w^{i}` with `i ≡ -1 (mod p)`. Bai's condition is exactly `deg K ≤ p - 2` (`int_cond_of_fract`).
-/

namespace PiIrrationality.BaiDeletion

open Polynomial

section Support

variable {R : Type*} [CommRing R]

/-- The coefficients of `f` vanish on the residue class `r` mod `p`. -/
def ZR (p r : ℕ) (f : PowerSeries R) : Prop := ∀ i, i % p = r → PowerSeries.coeff i f = 0

/-- `f` is supported on multiples of `p` (a power series in `w^p`). -/
def PS (p : ℕ) (f : PowerSeries R) : Prop := ∀ i, ¬ p ∣ i → PowerSeries.coeff i f = 0

theorem zr_mul {p r : ℕ} {A B : PowerSeries R} (hA : PS p A) (hB : ZR p r B) :
    ZR p r (A * B) := by
  intro i hi
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  by_cases h : p ∣ x.1
  · obtain ⟨k, hk⟩ := h
    have h2 : x.2 % p = r := by rw [← hi, ← hx, hk, Nat.mul_add_mod]
    rw [hB x.2 h2, mul_zero]
  · rw [hA x.1 h, zero_mul]

/-- Cancellation of a `p`-supported factor with unit constant term. -/
theorem zr_cancel {p r : ℕ} {V G : PowerSeries R} (hV : PS p V)
    (hV0 : IsUnit (PowerSeries.coeff 0 V)) (h : ZR p r (V * G)) : ZR p r G := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have key := h i hi
    rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, i)] at key
    · exact hV0.mul_right_eq_zero.mp key
    · intro x hx hne
      rw [Finset.mem_antidiagonal] at hx
      by_cases h1 : p ∣ x.1
      · have hx1 : x.1 ≠ 0 := by
          intro h0
          apply hne
          refine Prod.ext h0 ?_
          simp only
          omega
        obtain ⟨k, hk⟩ := h1
        have hlt : x.2 < i := by omega
        have hr : x.2 % p = r := by rw [← hi, ← hx, hk, Nat.mul_add_mod]
        rw [ih x.2 hlt hr, mul_zero]
      · rw [hV x.1 h1, zero_mul]
    · intro hni
      exact absurd (Finset.mem_antidiagonal.mpr (by simp)) hni

end Support

section Fp

variable {p : ℕ} [Fact p.Prime]

/-- A `p`-th power of a polynomial over `𝔽_p` is a polynomial in `w^p`. -/
theorem ps_coe_pow_p (f : (ZMod p)[X]) : PS p ((f ^ p : (ZMod p)[X]) : PowerSeries (ZMod p)) := by
  intro i hi
  rw [Polynomial.coeff_coe, ← ZMod.expand_card, Polynomial.coeff_expand (Fact.out : p.Prime).pos,
    if_neg hi]

/-- Coefficients of a derivative vanish at exponents `≡ -1 (mod p)`. -/
theorem coeff_derivative_eq_zero (f : (ZMod p)[X]) (i : ℕ) (hi : (i + 1) % p = 0) :
    (derivative f).coeff i = 0 := by
  rw [coeff_derivative]
  have h : ((i + 1 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff (i + 1) p).mpr (Nat.dvd_of_mod_eq_zero hi)
  push_cast at h
  rw [h, mul_zero]

/-- `(2w-1) v^k` with `v = w - w²` is `-(k+1)⁻¹ d/dw v^{k+1}`. -/
theorem coeff_twoX_mul_W_pow (k : ℕ) (hk : k + 1 < p) (i : ℕ) (hi : (i + 1) % p = 0) :
    ((2 * X - 1) * (X - X ^ 2) ^ k : (ZMod p)[X]).coeff i = 0 := by
  have hder : derivative ((X - X ^ 2 : (ZMod p)[X]) ^ (k + 1)) =
      -(C ((k + 1 : ℕ) : ZMod p) * ((2 * X - 1) * (X - X ^ 2) ^ k)) := by
    rw [derivative_pow, derivative_sub, derivative_X, derivative_X_pow]
    simp only [Nat.add_sub_cancel, Nat.cast_ofNat, map_ofNat]
    ring
  have h1 := coeff_derivative_eq_zero ((X - X ^ 2 : (ZMod p)[X]) ^ (k + 1)) i hi
  rw [hder, coeff_neg, coeff_C_mul, neg_eq_zero] at h1
  have hu : ((k + 1 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hd => absurd (Nat.le_of_dvd (Nat.succ_pos k) hd) (by omega)
  exact (mul_eq_zero.mp h1).resolve_left hu

/-- `Q(w) = 25w⁴ - 50w³ + 39w² - 14w + 2` over `𝔽_p`. -/
noncomputable def Qp (p : ℕ) : (ZMod p)[X] := 25 * X ^ 4 - 50 * X ^ 3 + 39 * X ^ 2 - 14 * X + 2

/-- The core vanishing: for odd `E` with `E + 4 r_b < 2 r_c`, the polynomial
`(2w-1)^E Q(w)^{r_b} (1-w)^{p-1-r_c}` has no monomials `w^i` with `i ≡ r_c (mod p)`. -/
theorem core_vanish (E rb rc : ℕ) (hE : E % 2 = 1) (hrc : rc < p)
    (hdeg : E + 4 * rb < 2 * rc) (i : ℕ) (hi : i % p = rc) :
    ((2 * X - 1) ^ E * Qp p ^ rb * (1 - X) ^ (p - 1 - rc) : (ZMod p)[X]).coeff i = 0 := by
  set s := p - 1 - rc with hs
  set e := E / 2 with he
  have hE' : E = 2 * e + 1 := by omega
  set K : (ZMod p)[X] := X ^ s * (1 - 4 * X) ^ e * (25 * X ^ 2 - 14 * X + 2) ^ rb with hK
  have hKdeg : K.natDegree ≤ s + e + 2 * rb := by
    have h1 : (1 - 4 * X : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
    have h2 : (25 * X ^ 2 - 14 * X + 2 : (ZMod p)[X]).natDegree ≤ 2 := by compute_degree
    calc K.natDegree
        ≤ (X ^ s * (1 - 4 * X) ^ e : (ZMod p)[X]).natDegree +
            ((25 * X ^ 2 - 14 * X + 2 : (ZMod p)[X]) ^ rb).natDegree := natDegree_mul_le
      _ ≤ ((X : (ZMod p)[X]) ^ s).natDegree + ((1 - 4 * X : (ZMod p)[X]) ^ e).natDegree +
            ((25 * X ^ 2 - 14 * X + 2 : (ZMod p)[X]) ^ rb).natDegree := by
          gcongr
          exact natDegree_mul_le
      _ ≤ s + e * 1 + rb * 2 := by
          gcongr
          · exact natDegree_X_pow_le s
          · exact natDegree_pow_le_of_le e h1
          · exact natDegree_pow_le_of_le rb h2
      _ = s + e + 2 * rb := by ring
  have hid : (X ^ s * ((2 * X - 1) ^ E * Qp p ^ rb * (1 - X) ^ s) : (ZMod p)[X]) =
      (2 * X - 1) * K.comp (X - X ^ 2) := by
    have hc : K.comp (X - X ^ 2) = (X - X ^ 2) ^ s * (1 - 4 * (X - X ^ 2)) ^ e *
        (25 * (X - X ^ 2) ^ 2 - 14 * (X - X ^ 2) + 2) ^ rb := by
      simp only [hK, mul_comp, pow_comp, X_comp, sub_comp, one_comp, add_comp, ofNat_comp, Nat.cast_ofNat]
    have hW : (X - X ^ 2 : (ZMod p)[X]) = X * (1 - X) := by ring
    have h4 : (1 - 4 * (X - X ^ 2) : (ZMod p)[X]) = (2 * X - 1) ^ 2 := by ring
    have hQ : (25 * (X - X ^ 2) ^ 2 - 14 * (X - X ^ 2) + 2 : (ZMod p)[X]) = Qp p := by
      unfold Qp; ring
    rw [hc, h4, hQ, hW, mul_pow, ← pow_mul, hE']
    ring
  have hdvd : (i + s + 1) % p = 0 := by
    have hmle := Nat.mod_le i p
    have h3 : i + s + 1 = (i - i % p) + p := by omega
    rw [h3]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_sub_mod i) dvd_rfl)
  have hD : ((2 * X - 1) * K.comp (X - X ^ 2)).coeff (i + s) = 0 := by
    rw [Polynomial.comp, eval₂_eq_sum_range, Finset.mul_sum, finsetSum_coeff]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [mul_left_comm, coeff_C_mul, coeff_twoX_mul_W_pow k (by omega) (i + s) hdvd, mul_zero]
  rw [← hid, coeff_X_pow_mul] at hD
  exact hD

end Fp

section Assembly

variable {p : ℕ} [Fact p.Prime]

theorem zr_main (A B Cc E q β rb γ rc : ℕ)
    (hA : p + 2 * A = E + 2 * p * q) (hB : B = p * β + rb) (hC : Cc = p * γ + rc) (hrc : rc < p)
    (hE : E % 2 = 1) (hdeg : E + 4 * rb < 2 * rc) :
    ZR p rc ((((2 * X - 1) ^ (2 * A) * Qp p ^ B : (ZMod p)[X]) : PowerSeries (ZMod p)) *
      (PowerSeries.invOneSubPow (ZMod p) (Cc + 1)).val) := by
  set s := p - 1 - rc with hs
  have hT : (((1 - X : (ZMod p)[X])) : PowerSeries (ZMod p)) = 1 - PowerSeries.X := by
    rw [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X]
  have hVps : PS p ((((1 - X) ^ (γ + 1) * (2 * X - 1)) ^ p : (ZMod p)[X]) : PowerSeries (ZMod p)) :=
    ps_coe_pow_p _
  have hV0 : IsUnit (PowerSeries.coeff 0
      ((((1 - X) ^ (γ + 1) * (2 * X - 1)) ^ p : (ZMod p)[X]) : PowerSeries (ZMod p))) := by
    rw [Polynomial.coeff_coe, coeff_zero_eq_eval_zero]
    have h0 : eval 0 (((1 - X) ^ (γ + 1) * (2 * X - 1)) ^ p : (ZMod p)[X]) = (-1) ^ p := by simp
    rw [h0]
    exact isUnit_neg_one.pow p
  refine zr_cancel hVps hV0 ?_
  have hexp : s + (Cc + 1) = p * (γ + 1) := by
    rw [hC, mul_add, mul_one]
    omega
  have hpoly : ((2 * X - 1 : (ZMod p)[X]) ^ p * ((2 * X - 1) ^ (2 * A) * Qp p ^ B) * (1 - X) ^ s) =
      ((2 * X - 1) ^ (2 * q) * Qp p ^ β) ^ p * ((2 * X - 1) ^ E * Qp p ^ rb * (1 - X) ^ s) := by
    rw [← mul_assoc, ← pow_add, hA, hB]
    ring
  have hVG : ((((1 - X) ^ (γ + 1) * (2 * X - 1)) ^ p : (ZMod p)[X]) : PowerSeries (ZMod p)) *
      ((((2 * X - 1) ^ (2 * A) * Qp p ^ B : (ZMod p)[X]) : PowerSeries (ZMod p)) *
        (PowerSeries.invOneSubPow (ZMod p) (Cc + 1)).val) =
      ((((2 * X - 1) ^ (2 * q) * Qp p ^ β) ^ p : (ZMod p)[X]) : PowerSeries (ZMod p)) *
        (((2 * X - 1) ^ E * Qp p ^ rb * (1 - X) ^ s : (ZMod p)[X]) : PowerSeries (ZMod p)) := by
    rw [← Polynomial.coe_mul, ← hpoly]
    simp only [Polynomial.coe_mul, Polynomial.coe_pow, hT]
    rw [← PowerSeries.one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow (ZMod p) s (Cc + 1), hexp]
    generalize (1 - PowerSeries.X : PowerSeries (ZMod p)) = T
    generalize ((2 * X - 1 : (ZMod p)[X]) : PowerSeries (ZMod p)) = Y
    ring
  rw [hVG]
  refine zr_mul (ps_coe_pow_p _) ?_
  intro i hi
  rw [Polynomial.coeff_coe]
  exact core_vanish E rb rc hE hrc hdeg i hi

omit [Fact p.Prime] in
/-- Bai's fractional-part condition, cleared of denominators. -/
theorem int_cond_of_fract {A B Cc : ℕ} (hp : 0 < p)
    (hfr : Int.fract ((A : ℚ) / p + 1 / 2) + 2 * Int.fract ((B : ℚ) / p) <
      Int.fract ((Cc : ℚ) / p)) :
    (p + 2 * A) % (2 * p) + 4 * (B % p) < 2 * (Cc % p) := by
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp
  have e0 : (A : ℚ) / p + 1 / 2 = ((p + 2 * A : ℕ) : ℚ) / ((2 * p : ℕ) : ℚ) := by
    push_cast
    field_simp
    ring
  rw [e0, Int.fract_div_natCast_eq_div_natCast_mod, Int.fract_div_natCast_eq_div_natCast_mod,
    Int.fract_div_natCast_eq_div_natCast_mod] at hfr
  have h2 : ((2 * p : ℕ) : ℚ) = 2 * p := by push_cast; ring
  rw [h2] at hfr
  have key : (((p + 2 * A) % (2 * p) : ℕ) : ℚ) + 4 * ((B % p : ℕ) : ℚ) <
      2 * ((Cc % p : ℕ) : ℚ) := by
    have hm := mul_lt_mul_of_pos_left hfr (by positivity : (0 : ℚ) < 2 * p)
    have l1 : (2 * (p : ℚ)) * ((((p + 2 * A) % (2 * p) : ℕ) : ℚ) / (2 * p) +
        2 * (((B % p : ℕ) : ℚ) / p)) =
        (((p + 2 * A) % (2 * p) : ℕ) : ℚ) + 4 * ((B % p : ℕ) : ℚ) := by
      field_simp
      ring
    have l2 : (2 * (p : ℚ)) * (((Cc % p : ℕ) : ℚ) / p) = 2 * ((Cc % p : ℕ) : ℚ) := by
      field_simp
    linarith
  exact_mod_cast key

/-- The deletion lemma in `𝔽_p[[w]]`, for variable exponents `A = an`, `B = bn`, `C = cn`. -/
theorem zr_of_fract (A B Cc : ℕ) (hp2 : p ≠ 2)
    (hfr : Int.fract ((A : ℚ) / p + 1 / 2) + 2 * Int.fract ((B : ℚ) / p) <
      Int.fract ((Cc : ℚ) / p)) :
    ZR p (Cc % p) ((((2 * X - 1) ^ (2 * A) * Qp p ^ B : (ZMod p)[X]) : PowerSeries (ZMod p)) *
      (PowerSeries.invOneSubPow (ZMod p) (Cc + 1)).val) := by
  have hp : p.Prime := Fact.out
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hkey := int_cond_of_fract hp.pos hfr
  refine zr_main A B Cc ((p + 2 * A) % (2 * p)) ((p + 2 * A) / (2 * p)) (B / p) (B % p) (Cc / p)
    (Cc % p) (Nat.mod_add_div (p + 2 * A) (2 * p)).symm (Nat.div_add_mod B p).symm
    (Nat.div_add_mod Cc p).symm (Nat.mod_lt _ hp.pos) ?_ hkey
  rw [Nat.mod_mod_of_dvd _ (dvd_mul_right 2 p)]
  omega

end Assembly

end PiIrrationality.BaiDeletion

namespace PiIrrationality.BaiGen

open Polynomial PiIrrationality.BaiDeletion

/-- `g_{n,m} mod p` is the `w^m` coefficient of the reduced series in `𝔽_p[[w]]`. -/
theorem g_cast (a b c n m p : ℕ) [Fact p.Prime] :
    ((g a b c n m : ℤ) : ZMod p) = PowerSeries.coeff m
      ((((2 * X - 1) ^ (2 * (a * n)) * Qp p ^ (b * n) : (ZMod p)[X]) : PowerSeries (ZMod p)) *
        (PowerSeries.invOneSubPow (ZMod p) (c * n + 1)).val) := by
  have hH : (Hw a b n).map (Int.castRingHom (ZMod p)) =
      (2 * X - 1) ^ (2 * (a * n)) * Qp p ^ (b * n) := by
    simp [Hw, Qw, Qp, Polynomial.map_pow, mul_assoc]
  have hcoe : PowerSeries.map (Int.castRingHom (ZMod p)) ((Hw a b n : ℤ[X]) : PowerSeries ℤ) =
      (((Hw a b n).map (Int.castRingHom (ZMod p)) : (ZMod p)[X]) : PowerSeries (ZMod p)) := by
    ext k
    simp [PowerSeries.coeff_map]
  have hinv : PowerSeries.map (Int.castRingHom (ZMod p)) (PowerSeries.invOneSubPow ℤ (c * n + 1)).val =
      (PowerSeries.invOneSubPow (ZMod p) (c * n + 1)).val := by
    ext k
    simp [PowerSeries.coeff_map, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
  unfold g Gw
  rw [show ((PowerSeries.coeff m ((Hw a b n : PowerSeries ℤ) *
      (PowerSeries.invOneSubPow ℤ (c * n + 1)).val) : ℤ) : ZMod p) =
      Int.castRingHom (ZMod p) (PowerSeries.coeff m ((Hw a b n : PowerSeries ℤ) *
      (PowerSeries.invOneSubPow ℤ (c * n + 1)).val)) from rfl, ← PowerSeries.coeff_map, map_mul,
    hcoe, hinv, hH]

/-- Deletion for variable exponents: if `p` satisfies Bai's condition and `m ≡ cn (mod p)`,
then `p ∣ g_{n,m}`. -/
theorem g_dvd_of_fract (a b c n p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hfr : Int.fract (((a * n : ℕ) : ℚ) / p + 1 / 2) + 2 * Int.fract (((b * n : ℕ) : ℚ) / p) <
      Int.fract (((c * n : ℕ) : ℚ) / p))
    (m : ℕ) (hm : m % p = c * n % p) : (p : ℤ) ∣ g a b c n m := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, g_cast]
  exact zr_of_fract (a * n) (b * n) (c * n) hp2 hfr m hm

/-- **Bai Lemma 2.2 analogue (variable exponents).** For `p ∈ P_n` and `p ∣ j ≤ cn`,
`p ∣ g_{n, cn - j}`, i.e. `p` divides `10^{-j} c_{j,n}` up to powers of `2` and `5`. -/
theorem deletion (a b c n p : ℕ) (hp : p ∈ deletedPrimes a b c n) (j : ℤ) (hj : (p : ℤ) ∣ j)
    (hjc : j ≤ ((c * n : ℕ) : ℤ)) :
    (p : ℤ) ∣ g a b c n (((c * n : ℕ) : ℤ) - j).toNat := by
  simp only [deletedPrimes, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨-, hpp, hp5, -, hfr⟩ := hp
  have := Fact.mk hpp
  refine g_dvd_of_fract a b c n p (by omega) hfr _ ?_
  have h1 : ((((c * n : ℕ) : ℤ) - j).toNat : ℤ) = ((c * n : ℕ) : ℤ) - j :=
    Int.toNat_of_nonneg (by omega)
  obtain ⟨k, rfl⟩ := hj
  have h2 : (((((c * n : ℕ) : ℤ) - p * k).toNat % p : ℕ) : ℤ) = ((c * n % p : ℕ) : ℤ) := by
    rw [Int.natCast_mod, h1, Int.natCast_mod, sub_eq_add_neg, ← mul_neg,
      Int.add_mul_emod_self_left]
  exact_mod_cast h2

end PiIrrationality.BaiGen

namespace PiIrrationality.Bai

/-- **Bai Lemma 2.2 at `(1857, 3714, 5570)`**: for `p ∈ P_n` and `p ∣ j ≤ 5570 n`,
`p ∣ g_{n, 5570n - j}`. -/
theorem g_dvd (n p : ℕ) (hp : p ∈ deletedPrimes n) (j : ℤ) (hj : (p : ℤ) ∣ j)
    (hjc : j ≤ ((5570 * n : ℕ) : ℤ)) : (p : ℤ) ∣ g n (((5570 * n : ℕ) : ℤ) - j).toNat :=
  BaiGen.deletion 1857 3714 5570 n p hp j hj hjc

/-- **Bai Lemma 2.2, Laurent form**: for `n ≥ 1`, `p ∈ P_n`, `p ∣ j`:
`c_{j,n} = p · z · 10^j` with `z ∈ ℤ`, i.e. `10^{-j} c_{j,n} ∈ pℤ`. -/
theorem lc_mod (n p : ℕ) (hn : 1 ≤ n) (hp : p ∈ deletedPrimes n) (j : ℤ) (hj : (p : ℤ) ∣ j) :
    ∃ z : ℤ, lc n j = (p : ℚ) * z * (10 : ℚ) ^ j := by
  rw [lc_eq]
  split_ifs with hjc
  · obtain ⟨w, hw⟩ := g_dvd n p hp j hj hjc
    refine ⟨2 ^ (3716 * n - 1) * 5 ^ (2 * n) * w, ?_⟩
    rw [hw]
    have e1 : (2 : ℚ) ^ (3716 * (n : ℤ) + j - 1) = 2 ^ (3716 * n - 1) * 2 ^ j := by
      rw [show 3716 * (n : ℤ) + j - 1 = ((3716 * n - 1 : ℕ) : ℤ) + j by omega,
        zpow_add₀ two_ne_zero, zpow_natCast]
    have e2 : (5 : ℚ) ^ (2 * (n : ℤ) + j) = 5 ^ (2 * n) * 5 ^ j := by
      rw [show 2 * (n : ℤ) + j = ((2 * n : ℕ) : ℤ) + j by omega,
        zpow_add₀ (by norm_num : (5 : ℚ) ≠ 0), zpow_natCast]
    have e3 : (10 : ℚ) ^ j = 2 ^ j * 5 ^ j := by
      rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_zpow]
    rw [e1, e2, e3]
    push_cast
    ring
  · exact ⟨0, by simp⟩

/-- `Φ_n ∣ g_{n, 5570n}`. -/
theorem Phi_dvd_g (n : ℕ) : (Phi n : ℤ) ∣ g n (5570 * n) := by
  have hd : Phi n ∣ (g n (5570 * n)).natAbs := by
    unfold Phi
    apply Finset.prod_primes_dvd
    · intro q hq
      simp only [deletedPrimes, Finset.mem_filter] at hq
      exact hq.2.1.prime
    · intro q hq
      have h := g_dvd n q hq 0 (dvd_zero _) (by positivity)
      rw [sub_zero, Int.toNat_natCast] at h
      exact Int.ofNat_dvd_left.mp h
  exact Int.ofNat_dvd_left.mpr hd

/-- **`Φ_n ∣ c_{0,n}`** (Bai Lemma 2.2, "in particular"): for `n ≥ 1`,
`c_{0,n} = Φ_n · z` with `z ∈ ℤ`. -/
theorem Phi_dvd_lc0 (n : ℕ) (hn : 1 ≤ n) : ∃ z : ℤ, lc n 0 = (Phi n : ℚ) * z := by
  obtain ⟨w, hw⟩ := Phi_dvd_g n
  refine ⟨2 ^ (3716 * n - 1) * 5 ^ (2 * n) * w, ?_⟩
  rw [lc_eq, if_pos (by positivity)]
  simp only [sub_zero, add_zero, Int.toNat_natCast]
  rw [hw]
  have e1 : (2 : ℚ) ^ (3716 * (n : ℤ) - 1) = 2 ^ (3716 * n - 1) := by
    rw [show 3716 * (n : ℤ) - 1 = ((3716 * n - 1 : ℕ) : ℤ) by omega, zpow_natCast]
  have e2 : (5 : ℚ) ^ (2 * (n : ℤ)) = 5 ^ (2 * n) := by
    rw [show 2 * (n : ℤ) = ((2 * n : ℕ) : ℤ) by omega, zpow_natCast]
  rw [e1, e2]
  push_cast
  ring

end PiIrrationality.Bai
end

-- ===== inlined: scratch.research.campaign_pick.pi_stage2.Integrality =====
section
set_option autoImplicit false

/-!
# Polynomial-part integrality (Bai's Lemma 2.5 analogue), variable exponents

`Y_n = 2^{1-hn} L_n i ∫_{-1-2i}^{-1+2i} P_n(t) dt ∈ ℤ`, `L_n = lcm(1,…,d₀n)/Φ_n`.

Three integrality statements about the rational number `Y_n`, then a gcd argument:
* (odd primes, `w`-monomials) `2^A 5^B Y_n ∈ ℤ`: deleted primes `p ∣ k+1` divide `q_k` (Lemma 2.2);
* (the prime 5, `t`-monomials) `2^{hn} Φ_n Y_n ∈ ℤ`: `P_n ∈ ℤ[t]`, endpoints in `ℤ[i]`;
* (the prime 2, Taylor at `w₀`) `d Y_n ∈ ℤ` for an odd `d`: Lemma 2.4 (`beta_TI`).
-/

namespace PiIrrationality.BaiGen

open Polynomial Complex PiIrrationality.BaiPF PiIrrationality.PolyInt PiIrrationality.BaiTaylor

/-- `Y_n = 2^{1-hn} (lcm(1..d₀n)/Φ_n) i ∫_{-1-2i}^{-1+2i} P_n(t) dt`. -/
noncomputable def Ypoly (a b c n : ℕ) : ℂ :=
  2 / 2 ^ (h b c * n) * ((Nat.lcmUpto (d0 a b c * n) : ℂ) / (Phi a b c n : ℂ)) * I *
    Lam ((Pt a b c n).map (Int.castRingHom ℂ)) (-1 - 2 * I) (-1 + 2 * I)

/-! ## Integer-valued complex numbers -/

/-- `z` is an integer. -/
def IsZ (z : ℂ) : Prop := ∃ x : ℤ, z = x

theorem IsZ_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, IsZ (f i)) :
    IsZ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    obtain ⟨x, hx⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨y, hy⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact ⟨x + y, by rw [hx, hy]; push_cast; ring⟩

/-! ## Arithmetic of `Φ_n` and `lcm(1..d₀n)` -/

theorem mem_deletedPrimes {a b c n p : ℕ} (hp : p ∈ deletedPrimes a b c n) :
    p ≤ d0 a b c * n ∧ p.Prime ∧ 5 < p := by
  simp only [deletedPrimes, Finset.mem_filter, Finset.mem_range] at hp
  exact ⟨by omega, hp.2.1, hp.2.2.1⟩

theorem Phi_coprime_ten (a b c n : ℕ) : Nat.Coprime 10 (Phi a b c n) := by
  unfold Phi
  rw [Nat.coprime_prod_right_iff]
  intro p hp
  obtain ⟨-, hpr, h5⟩ := mem_deletedPrimes hp
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpr]
  intro hd
  rcases (Nat.Prime.dvd_mul hpr).1 (show p ∣ 2 * 5 by simpa using hd) with h | h
  · have := Nat.le_of_dvd (by norm_num) h; omega
  · have := Nat.le_of_dvd (by norm_num) h; omega

theorem Phi_odd (a b c n : ℕ) : Odd (Phi a b c n) := by
  have h2 : Nat.Coprime 2 (Phi a b c n) :=
    Nat.Coprime.coprime_dvd_left (by norm_num) (Phi_coprime_ten a b c n)
  rw [Nat.coprime_comm, Nat.coprime_two_right] at h2
  exact h2

theorem dvd_lcmUpto {m M : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ M) : m ∣ Nat.lcmUpto M :=
  Finset.dvd_lcm (Finset.mem_Icc.2 ⟨h1, h2⟩)

theorem d0_mul (a b c n : ℕ) (hcb : c ≤ 2 * b) :
    d0 a b c * n + 2 * (c * n) = 2 * a * n + 4 * (b * n) := by
  have e1 : (2 * a + 4 * b) * n = 2 * a * n + 4 * (b * n) := by ring
  have e2 : 2 * c * n = 2 * (c * n) := by ring
  have hle : 2 * c * n ≤ (2 * a + 4 * b) * n := Nat.mul_le_mul_right _ (by omega)
  rw [d0, Nat.sub_mul]
  omega

/-- `k + 1 ∣ lcm(1..d₀n)` below the degree bound of the polynomial parts. -/
theorem succ_dvd_L (a b c n m : ℕ) (hcb : c ≤ 2 * b)
    (hm : m ≤ 2 * a * n + 4 * (b * n) - 2 * (c * n + 1)) :
    (m + 1) ∣ Nat.lcmUpto (d0 a b c * n) := by
  have := d0_mul a b c n hcb
  by_cases h0 : m = 0
  · subst h0; exact one_dvd _
  · exact dvd_lcmUpto (by omega) (by omega)

/-! ## Deleted primes divide the coefficients `q_k` with `p ∣ k+1` -/

theorem prime_dvd_q (a b c n p k : ℕ) (hp : p ∈ deletedPrimes a b c n) (hk : p ∣ k + 1) :
    (p : ℤ) ∣ (Qp (Hw a b n) (c * n)).coeff k := by
  have hpr := (mem_deletedPrimes hp).2.1
  rw [coeff_Qp _ _ (Hw_comp a b n)]
  apply dvd_sub
  · have hj : (p : ℤ) ∣ -((k : ℤ) + 1) := by
      rw [dvd_neg]; exact_mod_cast hk
    have := deletion a b c n p hp (-((k : ℤ) + 1)) hj (by omega)
    rw [show ((((c * n : ℕ) : ℤ) - -((k : ℤ) + 1)).toNat) = c * n + 1 + k by omega] at this
    rwa [gc_eq]
  · apply Finset.dvd_sum
    intro i hi
    rw [Finset.mem_range] at hi
    rw [gc_eq]
    by_cases hpi : p ∣ c * n - i
    · apply Dvd.dvd.mul_right
      have := deletion a b c n p hp ((c * n - i : ℕ) : ℤ) (Int.natCast_dvd_natCast.2 hpi) (by omega)
      rwa [show ((((c * n : ℕ) : ℤ) - ((c * n - i : ℕ) : ℤ)).toNat) = i by omega] at this
    · apply Dvd.dvd.mul_left
      set r := c * n - i with hr
      have h1 : (r + k).choose (k + 1) * (k + 1) = (r + k).choose k * r := by
        rw [Nat.choose_succ_right_eq, Nat.add_sub_cancel]
      have h2 : p ∣ (r + k).choose k * r := h1 ▸ Dvd.dvd.mul_left hk _
      have h3 : p ∣ (r + k).choose k := (hpr.dvd_mul.1 h2).resolve_right hpi
      rw [Nat.choose_symm_add]
      exact_mod_cast h3

/-- `Φ_n (k+1) ∣ lcm(1..d₀n) q_k` whenever `k+1 ∣ lcm(1..d₀n)`. -/
theorem Phi_mul_dvd (a b c n k : ℕ) (hk : (k + 1) ∣ Nat.lcmUpto (d0 a b c * n)) :
    ((Phi a b c n : ℤ) * (k + 1)) ∣ (Nat.lcmUpto (d0 a b c * n) : ℤ) * (Qp (Hw a b n) (c * n)).coeff k := by
  obtain ⟨L', hL'⟩ := hk
  have hPhi : (Phi a b c n : ℤ) ∣ (L' : ℤ) * (Qp (Hw a b n) (c * n)).coeff k := by
    rw [Int.natCast_dvd]
    unfold Phi
    apply Finset.prod_primes_dvd
    · intro p hp; exact (mem_deletedPrimes hp).2.1.prime
    · intro p hp
      rw [← Int.natCast_dvd]
      obtain ⟨hpd, hpr, -⟩ := mem_deletedPrimes hp
      by_cases hpk : p ∣ k + 1
      · exact Dvd.dvd.mul_left (prime_dvd_q a b c n p k hp hpk) _
      · apply Dvd.dvd.mul_right
        have hpL : p ∣ (k + 1) * L' := hL' ▸ dvd_lcmUpto hpr.one_lt.le hpd
        exact_mod_cast (hpr.dvd_mul.1 hpL).resolve_left hpk
  rw [hL']
  push_cast
  rw [show ((k : ℤ) + 1) * L' * (Qp (Hw a b n) (c * n)).coeff k =
    ((k : ℤ) + 1) * (L' * (Qp (Hw a b n) (c * n)).coeff k) by ring, mul_comm (Phi a b c n : ℤ)]
  exact mul_dvd_mul_left _ hPhi

/-! ## (b) the prime 5: `P_n ∈ ℤ[t]` and the endpoints are Gaussian integers -/

theorem mul_div_aux (z y x w : ℂ) (hz : z ≠ 0) : z * y * (I * (x * (w / z))) = y * x * (I * w) := by
  field_simp

theorem L_mul_I_Lam_Pt (a b c n : ℕ) (hcb : c ≤ 2 * b) :
    IsZ ((Nat.lcmUpto (d0 a b c * n) : ℂ) *
      (I * Lam ((Pt a b c n).map (Int.castRingHom ℂ)) (-1 - 2 * I) (-1 + 2 * I))) := by
  set P := (Pt a b c n).map (Int.castRingHom ℂ) with hP
  have hdeg : P.natDegree ≤ 2 * a * n + 4 * (b * n) - 2 * (c * n + 1) :=
    (natDegree_map_le).trans (natDegree_Pt_le a b c n)
  rw [Lam_eq_sum P _ _ (P.natDegree + 1) (Nat.lt_succ_self _), Finset.mul_sum, Finset.mul_sum]
  apply IsZ_sum
  intro m hm
  rw [Finset.mem_range] at hm
  obtain ⟨L', hL'⟩ := succ_dvd_L a b c n m hcb (by omega)
  obtain ⟨v, hv⟩ := I_mul_pow_sub_int (-1 + 2 * I) (-1 - 2 * I) (-2) 5 4 (by push_cast; ring)
    (by push_cast; linear_combination (-4 : ℂ) * I_sq) (by push_cast; ring) (m + 1)
  refine ⟨(Pt a b c n).coeff m * v * L', ?_⟩
  have hm1 : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  rw [hL', hP, coeff_map]
  push_cast
  rw [mul_div_aux _ _ _ _ hm1, hv, eq_intCast]
  ring

/-! ## (a) the odd primes: deletion on the `w`-monomial coefficients -/

theorem term_aux (L q P y u F G z f e : ℂ) (hz : z ≠ 0) (hf : f ≠ 0) (hy : L * q = P * z * y)
    (hu : I * (F - G) = u) :
    L * (e * f * (I * (q * ((F / f - G / f) / z)))) = P * (y * u * e) := by
  calc L * (e * f * (I * (q * ((F / f - G / f) / z))))
      = (L * q) * e * (I * (F - G)) * (f * f⁻¹) * z⁻¹ := by ring
    _ = (P * z * y) * e * u * 1 * z⁻¹ := by rw [hy, hu, mul_inv_cancel₀ hf]
    _ = P * (y * u * e) * (z * z⁻¹) := by ring
    _ = P * (y * u * e) := by rw [mul_inv_cancel₀ hz, mul_one]

theorem L_mul_I_Lam_Q (a b c n : ℕ) (hcb : c ≤ 2 * b) :
    ∃ Z : ℤ, (Nat.lcmUpto (d0 a b c * n) : ℂ) * (5 ^ ((Qp (Hw a b n) (c * n)).natDegree + 1) *
      (I * Lam ((Qp (Hw a b n) (c * n)).map (Int.castRingHom ℂ)) ((2 - I) / 5) ((2 + I) / 5))) =
      (Phi a b c n : ℂ) * Z := by
  set Q := Qp (Hw a b n) (c * n) with hQ
  set M := Q.natDegree + 1 with hM
  have hdegQ : Q.natDegree ≤ 2 * a * n + 4 * (b * n) - 2 * (c * n + 1) :=
    (natDegree_Qp_le _ _ (Hw_comp a b n)).trans (Nat.sub_le_sub_right (natDegree_Hw_le a b n) _)
  rw [Lam_eq_sum _ _ _ M (by rw [hM]; exact Nat.lt_succ_of_le natDegree_map_le), Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum]
  have hterm : ∀ k ∈ Finset.range M, ∃ z : ℤ, (Nat.lcmUpto (d0 a b c * n) : ℂ) * (5 ^ M * (I *
      ((Q.map (Int.castRingHom ℂ)).coeff k *
        ((((2 + I) / 5) ^ (k + 1) - ((2 - I) / 5) ^ (k + 1)) / (k + 1))))) =
      (Phi a b c n : ℂ) * z := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkL := succ_dvd_L a b c n k hcb (by omega)
    obtain ⟨y, hy⟩ := Phi_mul_dvd a b c n k hkL
    obtain ⟨u, hu⟩ := I_mul_pow_sub_int (2 + I) (2 - I) 4 5 2 (by push_cast; ring)
      (by push_cast; linear_combination (-1 : ℂ) * I_sq) (by push_cast; ring) (k + 1)
    refine ⟨y * u * 5 ^ (M - (k + 1)), ?_⟩
    have hy' : (Nat.lcmUpto (d0 a b c * n) : ℂ) * (Q.coeff k : ℂ) =
        (Phi a b c n : ℂ) * ((k : ℂ) + 1) * y := by exact_mod_cast hy
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    rw [coeff_map, eq_intCast, show (5 : ℂ) ^ M = 5 ^ (M - (k + 1)) * 5 ^ (k + 1) by
      rw [← pow_add]; congr 1; omega, div_pow, div_pow]
    push_cast
    refine term_aux _ _ _ _ _ _ _ _ _ _ hk1 ?_ hy' hu
    exact pow_ne_zero _ (by norm_num)
  choose! z hz using hterm
  refine ⟨∑ k ∈ Finset.range M, z k, ?_⟩
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl hz

/-! ## (c) the prime 2: Lemma 2.4 (`beta_TI`) -/

theorem h_mul_eq (b c n : ℕ) (hc : Even c) (hcb : c ≤ 2 * b) :
    h b c * n + 5 * (c * n / 2) = 5 * (b * n) := by
  obtain ⟨c', rfl⟩ := hc
  have e1 : h b (c' + c') = 5 * b - 5 * c' := by unfold h; omega
  have e2 : (c' + c') * n / 2 = c' * n := by
    rw [show (c' + c') * n = 2 * (c' * n) by ring]; omega
  rw [e1, e2, Nat.sub_mul]
  have h5 : 5 * c' * n ≤ 5 * b * n := Nat.mul_le_mul_right _ (by omega)
  zify [h5]
  ring

theorem Ypoly_TI (a b c n : ℕ) (hc : Even c) (hcb : c ≤ 2 * b) : TI 0 (Ypoly a b c n) := by
  have hh := h_mul_eq b c n hc hcb
  have hcn : Even (c * n) := hc.mul_right n
  obtain ⟨r, hr⟩ := hcn
  have hΦ0 : (Phi a b c n : ℂ) ≠ 0 := by exact_mod_cast (Phi_odd a b c n).pos.ne'
  set Q := Qp (Hw a b n) (c * n) with hQ
  set S := (Q.map (Int.castRingHom ℂ)).comp (X + C w0) with hS
  have hdegS : S.natDegree ≤ 2 * a * n + 4 * (b * n) - 2 * (c * n + 1) := by
    refine (natDegree_comp_le).trans ?_
    have h1 : (X + C w0 : ℂ[X]).natDegree ≤ 1 := by compute_degree!
    have h2 : (Q.map (Int.castRingHom ℂ)).natDegree ≤ 2 * a * n + 4 * (b * n) - 2 * (c * n + 1) :=
      (natDegree_map_le).trans ((natDegree_Qp_le _ _ (Hw_comp a b n)).trans
        (Nat.sub_le_sub_right (natDegree_Hw_le a b n) _))
    calc _ ≤ (Q.map (Int.castRingHom ℂ)).natDegree * 1 := Nat.mul_le_mul le_rfl h1
      _ ≤ _ := by rw [mul_one]; exact h2
  have hYeq : Ypoly a b c n = 2 / 2 ^ (h b c * n) *
      ((Nat.lcmUpto (d0 a b c * n) : ℂ) / (Phi a b c n : ℂ)) * I *
      (10 * Kc a b c n * Lam S 0 ((2 + I) / 5 - w0)) := by
    rw [Ypoly, Lam_Pt, show (2 - I) / 5 = w0 from rfl, Lam_taylor]
  rw [hYeq, Lam_eq_sum S _ _ (S.natDegree + 1) (Nat.lt_succ_self _), Finset.mul_sum, Finset.mul_sum]
  apply TI_sum
  intro k hk
  rw [Finset.mem_range] at hk
  obtain ⟨L', hL'⟩ := succ_dvd_L a b c n k hcb (by omega)
  have hβ := beta_TI a b c n k ⟨r, hr⟩
  have hβ' : S.coeff k = beta (Hw a b n) (c * n) k := rfl
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hF : TI (((c * n / 2 : ℕ) : ℤ) - (b * n : ℕ)) (2 / 2 ^ (h b c * n) * 10 * Kc a b c n) := by
    have e : 2 / 2 ^ (h b c * n) * 10 * Kc a b c n = (20 : ℂ) * ((5 ^ (2 * a * n + 1) : ℕ) : ℂ) *
        (400 : ℂ) ^ (b * n) * ((100 : ℂ)⁻¹) ^ (c * n + 1) * (2 : ℂ) ^ (-((h b c * n : ℕ) : ℤ)) := by
      rw [Kc, zpow_neg, zpow_natCast, inv_pow]; push_cast; ring
    rw [e]
    have h20 : TI 2 (20 : ℂ) := ⟨1, odd_one, 5, 0, by push_cast; norm_num⟩
    have h400 : TI 4 (400 : ℂ) := ⟨1, odd_one, 25, 0, by push_cast; norm_num⟩
    have h100 : TI (-2) ((100 : ℂ)⁻¹) := ⟨25, by decide, 1, 0, by push_cast; norm_num⟩
    have := TI_mul (TI_mul (TI_mul (TI_mul h20 (TI_nat (5 ^ (2 * a * n + 1)))) (TI_pow h400 (b * n)))
      (TI_pow h100 (c * n + 1))) (TI_two_zpow (-((h b c * n : ℕ) : ℤ)))
    refine TI_congr ?_ this
    push_cast
    omega
  have h2I : TI 1 (2 * I) := ⟨1, odd_one, 0, 1, by push_cast; ring⟩
  have hR := TI_mul (TI_mul (TI_mul (TI_mul (TI_mul (TI_mul hF (TI_nat L'))
    (TI_inv_odd _ (Phi_odd a b c n))) TI_I) hβ) (TI_pow h2I (k + 1)))
    (TI_inv_odd (5 ^ (k + 1)) (Odd.pow (by decide)))
  have hR0 := TI_congr (show _ = (0 : ℤ) by push_cast; omega) hR
  convert hR0 using 1
  rw [hL', hβ', show (2 + I) / 5 - w0 = 2 * I / 5 by unfold w0; ring,
    zero_pow (by omega : k + 1 ≠ 0), sub_zero, div_pow]
  push_cast
  field_simp

/-! ## The theorem -/

theorem den_dvd_of_mul (q : ℚ) (m : ℕ) (hm : m ≠ 0) (x : ℤ) (h : (m : ℚ) * q = x) : q.den ∣ m := by
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hq : q = Rat.divInt x m := by
    rw [Rat.divInt_eq_div]
    push_cast
    rw [eq_div_iff hm', mul_comm, h]
  have := Rat.den_dvd x m
  rw [← hq] at this
  exact_mod_cast this

/-- **Polynomial-part integrality** (Bai's Lemma 2.5 analogue) for variable exponents:
`2^{1-hn} (lcm(1..d₀n)/Φ_n) i ∫_{-1-2i}^{-1+2i} P_n(t) dt ∈ ℤ` whenever `c` is even and `c ≤ 2b`. -/
theorem Ypoly_int (a b c n : ℕ) (hc : Even c) (hcb : c ≤ 2 * b) : ∃ z : ℤ, Ypoly a b c n = z := by
  have hΦpos : 0 < Phi a b c n := (Phi_odd a b c n).pos
  have hΦ0 : (Phi a b c n : ℂ) ≠ 0 := by exact_mod_cast hΦpos.ne'
  have hΦq : (Phi a b c n : ℚ) ≠ 0 := by exact_mod_cast hΦpos.ne'
  obtain ⟨Zb, hZb⟩ := L_mul_I_Lam_Pt a b c n hcb
  obtain ⟨Za, hZa⟩ := L_mul_I_Lam_Q a b c n hcb
  obtain ⟨q, hq⟩ : ∃ q : ℚ, q = 2 * Zb / (2 ^ (h b c * n) * Phi a b c n) := ⟨_, rfl⟩
  -- (b): `2^{hn} Φ Y ∈ ℤ`
  have hYq : Ypoly a b c n = (q : ℂ) := by
    have e : Ypoly a b c n = 2 / ((2 : ℂ) ^ (h b c * n) * Phi a b c n) *
        ((Nat.lcmUpto (d0 a b c * n) : ℂ) *
          (I * Lam ((Pt a b c n).map (Int.castRingHom ℂ)) (-1 - 2 * I) (-1 + 2 * I))) := by
      rw [Ypoly]; ring
    rw [e, hZb, hq]; push_cast; ring
  have hb : ((2 ^ (h b c * n) * Phi a b c n : ℕ) : ℚ) * q = ((2 * Zb : ℤ) : ℚ) := by
    rw [hq]; push_cast; field_simp
  -- (a): `100^{cn+1} 5^M 2^{hn} Y ∈ ℤ`
  have e1 : Ypoly a b c n * ((2 : ℂ) ^ (h b c * n) * Phi a b c n) = 20 * Kc a b c n *
      ((Nat.lcmUpto (d0 a b c * n) : ℂ) *
        (I * Lam ((Qp (Hw a b n) (c * n)).map (Int.castRingHom ℂ)) ((2 - I) / 5) ((2 + I) / 5))) := by
    rw [Ypoly, Lam_Pt]; field_simp; ring
  have e2 : (5 : ℂ) ^ ((Qp (Hw a b n) (c * n)).natDegree + 1) *
      (Ypoly a b c n * ((2 : ℂ) ^ (h b c * n) * Phi a b c n)) =
      20 * Kc a b c n * (Phi a b c n * Za) := by
    rw [e1, ← hZa]; ring
  have e3 : (100 : ℂ) ^ (c * n + 1) * ((5 : ℂ) ^ ((Qp (Hw a b n) (c * n)).natDegree + 1) *
      (Ypoly a b c n * ((2 : ℂ) ^ (h b c * n) * Phi a b c n))) =
      20 * 5 ^ (2 * a * n + 1) * 400 ^ (b * n) * (Phi a b c n * Za) := by
    rw [e2, Kc]; field_simp
  have ea : ((100 ^ (c * n + 1) * 5 ^ ((Qp (Hw a b n) (c * n)).natDegree + 1) *
      2 ^ (h b c * n) : ℕ) : ℂ) * Ypoly a b c n =
      ((20 * 5 ^ (2 * a * n + 1) * 400 ^ (b * n) * Za : ℤ) : ℂ) := by
    push_cast
    apply mul_right_cancel₀ hΦ0
    linear_combination e3
  have ha : ((100 ^ (c * n + 1) * 5 ^ ((Qp (Hw a b n) (c * n)).natDegree + 1) *
      2 ^ (h b c * n) : ℕ) : ℚ) * q = ((20 * 5 ^ (2 * a * n + 1) * 400 ^ (b * n) * Za : ℤ) : ℚ) := by
    rw [hYq] at ea; exact_mod_cast ea
  -- (c): `d Y ∈ ℤ` for an odd `d`
  have hc' := Ypoly_TI a b c n hc hcb
  rw [hYq] at hc'
  obtain ⟨d, hd, x, hx⟩ := TI_rat q hc'
  -- denominators
  generalize (Qp (Hw a b n) (c * n)).natDegree + 1 = M at ha
  generalize h b c * n = HN at ha hb
  generalize c * n + 1 = N1 at ha
  have hd1 := den_dvd_of_mul q d (by rintro rfl; exact Nat.not_odd_zero hd) x hx
  have hb1 := den_dvd_of_mul q (2 ^ HN * Phi a b c n) (Nat.mul_pos (by positivity) hΦpos).ne' _ hb
  have ha1 := den_dvd_of_mul q (100 ^ N1 * 5 ^ M * 2 ^ HN) (by positivity) _ ha
  have hc2 : Nat.Coprime q.den 2 :=
    Nat.Coprime.coprime_dvd_left hd1 (Nat.coprime_two_right.2 hd)
  have hc5 : Nat.Coprime 5 (Phi a b c n) :=
    Nat.Coprime.coprime_dvd_left (by norm_num) (Phi_coprime_ten a b c n)
  have hdΦ : q.den ∣ Phi a b c n := (Nat.Coprime.pow_right HN hc2).dvd_of_dvd_mul_left hb1
  have h100 : 100 ^ N1 * 5 ^ M * 2 ^ HN = (2 ^ HN * 4 ^ N1) * (25 ^ N1 * 5 ^ M) := by
    rw [show (100 : ℕ) = 4 * 25 by norm_num, mul_pow]; ring
  rw [h100] at ha1
  have hc4 : Nat.Coprime q.den (4 ^ N1) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; exact Nat.Coprime.pow_right _ hc2
  have hc24 : Nat.Coprime q.den (2 ^ HN * 4 ^ N1) :=
    Nat.Coprime.mul_right (Nat.Coprime.pow_right _ hc2) hc4
  have hd5 : q.den ∣ 25 ^ N1 * 5 ^ M := hc24.dvd_of_dvd_mul_left ha1
  have h25 : Nat.Coprime (25 ^ N1) (Phi a b c n) := by
    rw [show (25 : ℕ) = 5 ^ 2 by norm_num, ← pow_mul]; exact Nat.Coprime.pow_left _ hc5
  have hcopΦ : Nat.Coprime (25 ^ N1 * 5 ^ M) (Phi a b c n) :=
    Nat.coprime_mul_iff_left.2 ⟨h25, Nat.Coprime.pow_left _ hc5⟩
  have hden : q.den = 1 := Nat.eq_one_of_dvd_coprimes hcopΦ hd5 hdΦ
  refine ⟨q.num, ?_⟩
  have hqn : (q.num : ℚ) = q := Rat.coe_int_num_of_den_eq_one hden
  rw [hYq]
  calc (q : ℂ) = ((q.num : ℚ) : ℂ) := by rw [hqn]
    _ = (q.num : ℂ) := by norm_cast

end PiIrrationality.BaiGen
end

-- ===== inlined: scratch.research.campaign_pick.pi_stage3.PoleInt =====
section
set_option autoImplicit false

/-!
# Pole-term integrality (Bai Lemmas 2.1, 2.3, 2.6 analogues) and the `π`-coefficient (stage 3)

`c_{j,n} = K_n 10^{j+1} g_{n,cn-j} = 2^{(4b-2c)n-1} 5^{2(a+b-c)n} 10^j g_{n,cn-j}` (`cc`).
For `1 ≤ m ≤ cn` the `m`-th rational pole term of `M_n J_n`,
`M_n i (c_{m,n}/m) [(6-2i)^{-m} - (4+2i)^{-m} - (6+2i)^{-m} + (4-2i)^{-m}]`, is an integer:
* `(4∓2i)^{-1} = (2±i)/10`, `(6∓2i)^{-1} = (3±i)/20`;
* `i((2+i)^m - (2-i)^m) ∈ ℤ`, `i((3+i)^m - (3-i)^m) ∈ 2^{⌊m/2⌋} ℤ` (`(3+i)² = 2(4+3i)`);
* `Φ_n m ∣ lcm(1..d₀n) g_{n,cn-m}` (deletion, Lemma 2.3), and `2^{bn-⌊(cn-m)/2⌋} ∣ g_{n,cn-m}`.
The `j = 0` term gives `V_n = -M_n c_{0,n}/2 ∈ ℤ`.
-/

namespace PiIrrationality.BaiGen

open Complex Polynomial PiIrrationality.PolyInt PiIrrationality.BaiTwo

/-- The complex Laurent coefficient `c_{j,n} = K_n 10^{j+1} g_{n,cn-j}` of `(5±t)^{-(j+1)}`. -/
noncomputable def cc (a b c n j : ℕ) : ℂ := Kc a b c n * 10 ^ (j + 1) * (g a b c n (c * n - j) : ℂ)

theorem M_cplx (a b c n : ℕ) : ((M a b c n : ℝ) : ℂ) =
    2 ^ 4 * (Nat.lcmUpto (d0 a b c * n) : ℂ) / (2 ^ (h b c * n) * (Phi a b c n : ℂ)) := by
  unfold M; push_cast; ring

theorem expo_facts (a b c n : ℕ) (hcb : c < 2 * b) (hab : c ≤ a + b) :
    c * n + n ≤ 2 * (b * n) ∧ c * n ≤ a * n + b * n := by
  constructor
  · have := Nat.mul_le_mul_right n (show c + 1 ≤ 2 * b by omega)
    rwa [add_mul, one_mul, mul_assoc] at this
  · have := Nat.mul_le_mul_right n hab
    rwa [add_mul] at this

/-- `K_n · 10 = 2^{4bn-2cn-1} 5^{2an+2bn-2cn}`. -/
theorem Kc_mul_ten (a b c n : ℕ) (hcb : c < 2 * b) (hab : c ≤ a + b) (hn : 1 ≤ n) :
    Kc a b c n * 10 =
      2 ^ (4 * (b * n) - 2 * (c * n) - 1) * 5 ^ (2 * (a * n) + 2 * (b * n) - 2 * (c * n)) := by
  obtain ⟨h1, h2⟩ := expo_facts a b c n hcb hab
  have E2 : 4 * (b * n) + 1 = (4 * (b * n) - 2 * (c * n) - 1) + 2 * (c * n + 1) := by omega
  have E5 : 2 * a * n + 1 + 2 * (b * n) + 1 =
      (2 * (a * n) + 2 * (b * n) - 2 * (c * n)) + 2 * (c * n + 1) := by
    have : 2 * a * n = 2 * (a * n) := by ring
    omega
  unfold Kc
  rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ (by norm_num))]
  have h400 : (400 : ℂ) ^ (b * n) = 2 ^ (4 * (b * n)) * 5 ^ (2 * (b * n)) := by
    rw [show (400 : ℂ) = 2 ^ 4 * 5 ^ 2 by norm_num, mul_pow, ← pow_mul, ← pow_mul]
  have h100 : (100 : ℂ) ^ (c * n + 1) = 2 ^ (2 * (c * n + 1)) * 5 ^ (2 * (c * n + 1)) := by
    rw [show (100 : ℂ) = 2 ^ 2 * 5 ^ 2 by norm_num, mul_pow, ← pow_mul, ← pow_mul]
  rw [h400, h100]
  calc (5 : ℂ) ^ (2 * a * n + 1) * (2 ^ (4 * (b * n)) * 5 ^ (2 * (b * n))) * 10
      = 2 ^ (4 * (b * n) + 1) * 5 ^ (2 * a * n + 1 + 2 * (b * n) + 1) := by ring
    _ = _ := by rw [E2, E5]; ring

/-! ## Gaussian integers -/

/-- `z ∈ ℤ[i]`. -/
def GI (z : ℂ) : Prop := ∃ x y : ℤ, z = x + y * I

theorem GI_mul {z w : ℂ} (hz : GI z) (hw : GI w) : GI (z * w) := by
  obtain ⟨x, y, rfl⟩ := hz
  obtain ⟨x', y', rfl⟩ := hw
  exact ⟨x * x' - y * y', x * y' + y * x', by push_cast; linear_combination ((y : ℂ) * y') * I_sq⟩

theorem GI_pow {z : ℂ} (hz : GI z) (m : ℕ) : GI (z ^ m) := by
  induction m with
  | zero => exact ⟨1, 0, by simp⟩
  | succ m ih => rw [pow_succ]; exact GI_mul ih hz

theorem GI_sub_conj {z : ℂ} (hz : GI z) : ∃ k : ℤ, I * (z - starRingEnd ℂ z) = k := by
  obtain ⟨x, y, rfl⟩ := hz
  refine ⟨-2 * y, ?_⟩
  apply Complex.ext <;> simp <;> ring

theorem X_int (m : ℕ) : ∃ x : ℤ, I * ((2 + I) ^ m - (2 - I) ^ m) = x := by
  have hc : (2 - I : ℂ) ^ m = starRingEnd ℂ ((2 + I) ^ m) := by
    rw [map_pow]; congr 1; apply Complex.ext <;> simp
  rw [hc]
  exact GI_sub_conj (GI_pow ⟨2, 1, by push_cast; ring⟩ m)

theorem Y_int (m : ℕ) : ∃ y : ℤ, I * ((3 + I) ^ m - (3 - I) ^ m) = 2 ^ (m / 2) * y := by
  have hsplit : (3 + I : ℂ) ^ m = 2 ^ (m / 2) * ((4 + 3 * I) ^ (m / 2) * (3 + I) ^ (m % 2)) := by
    conv_lhs => rw [← Nat.div_add_mod m 2]
    rw [pow_add, pow_mul, show (3 + I : ℂ) ^ 2 = 2 * (4 + 3 * I) by linear_combination I_sq, mul_pow]
    ring
  have hc : (3 - I : ℂ) ^ m = starRingEnd ℂ ((3 + I) ^ m) := by
    rw [map_pow]; congr 1; apply Complex.ext <;> simp
  have hG : GI ((4 + 3 * I) ^ (m / 2) * (3 + I) ^ (m % 2)) :=
    GI_mul (GI_pow ⟨4, 3, by push_cast; ring⟩ _) (GI_pow ⟨3, 1, by push_cast; ring⟩ _)
  obtain ⟨y, hy⟩ := GI_sub_conj hG
  refine ⟨y, ?_⟩
  rw [hc, hsplit, map_mul, map_pow, map_ofNat]
  linear_combination (2 : ℂ) ^ (m / 2) * hy

/-! ## The endpoint bracket -/

theorem inv_four_sub : ((4 : ℂ) - 2 * I)⁻¹ = (2 + I) / 10 :=
  inv_eq_of_mul_eq_one_right (by linear_combination (-1 / 5 : ℂ) * I_sq)

theorem inv_four_add : ((4 : ℂ) + 2 * I)⁻¹ = (2 - I) / 10 :=
  inv_eq_of_mul_eq_one_right (by linear_combination (-1 / 5 : ℂ) * I_sq)

theorem inv_six_sub : ((6 : ℂ) - 2 * I)⁻¹ = (3 + I) / 20 :=
  inv_eq_of_mul_eq_one_right (by linear_combination (-1 / 10 : ℂ) * I_sq)

theorem inv_six_add : ((6 : ℂ) + 2 * I)⁻¹ = (3 - I) / 20 :=
  inv_eq_of_mul_eq_one_right (by linear_combination (-1 / 10 : ℂ) * I_sq)

theorem bracket_eq (m : ℕ) :
    (((6 - 2 * I) ^ m)⁻¹ - ((4 + 2 * I) ^ m)⁻¹) - (((6 + 2 * I) ^ m)⁻¹ - ((4 - 2 * I) ^ m)⁻¹) =
      ((2 + I) ^ m - (2 - I) ^ m) / 10 ^ m + ((3 + I) ^ m - (3 - I) ^ m) / 20 ^ m := by
  rw [← inv_pow, ← inv_pow, ← inv_pow, ← inv_pow, inv_six_sub, inv_four_add, inv_six_add,
    inv_four_sub, div_pow, div_pow, div_pow, div_pow]
  ring

/-! ## Deleted primes and the reduced lcm (Bai Lemma 2.3) -/

theorem two_coprime_Phi (a b c n : ℕ) : IsCoprime (2 : ℤ) (Phi a b c n : ℤ) := by
  have := Nat.isCoprime_iff_coprime.2 (Nat.coprime_two_left.2 (Phi_odd a b c n))
  simpa using this

/-- `lcm(1..d₀n) g_{n,cn-m} = Φ_n m 2^{bn-⌊(cn-m)/2⌋} K`. -/
theorem lcm_g_eq (a b c n m : ℕ) (hm1 : 1 ≤ m) (hmd : m ≤ d0 a b c * n) (hmN : m ≤ c * n) :
    ∃ K : ℤ, (Nat.lcmUpto (d0 a b c * n) : ℤ) * g a b c n (c * n - m) =
      (Phi a b c n : ℤ) * m * (2 ^ (b * n - (c * n - m) / 2) * K) := by
  obtain ⟨L', hL'⟩ := dvd_lcmUpto hm1 hmd
  have hPhi : (Phi a b c n : ℤ) ∣ (L' : ℤ) * g a b c n (c * n - m) := by
    rw [Int.natCast_dvd]
    unfold Phi
    apply Finset.prod_primes_dvd
    · intro p hp; exact (mem_deletedPrimes hp).2.1.prime
    · intro p hp
      rw [← Int.natCast_dvd]
      obtain ⟨hpd, hpr, -⟩ := mem_deletedPrimes hp
      by_cases hpm : p ∣ m
      · apply Dvd.dvd.mul_left
        have := deletion a b c n p hp (m : ℤ) (Int.natCast_dvd_natCast.2 hpm) (by exact_mod_cast hmN)
        rwa [← Nat.cast_sub hmN, Int.toNat_natCast] at this
      · apply Dvd.dvd.mul_right
        have hpL : p ∣ m * L' := hL' ▸ dvd_lcmUpto hpr.one_lt.le hpd
        exact_mod_cast (hpr.dvd_mul.1 hpL).resolve_left hpm
  obtain ⟨K0, hK0⟩ := hPhi
  have h2 : (2 : ℤ) ^ (b * n - (c * n - m) / 2) ∣ K0 * (Phi a b c n : ℤ) := by
    rw [mul_comm K0, ← hK0]
    exact Dvd.dvd.mul_left (g_two_adic a b c n (c * n - m)) _
  obtain ⟨K, hK⟩ := ((two_coprime_Phi a b c n).pow_left).dvd_of_dvd_mul_right h2
  refine ⟨K, ?_⟩
  rw [hL']
  push_cast
  rw [hK] at hK0
  linear_combination (m : ℤ) * hK0

/-! ## Bai Lemma 2.1 (2- and 5-adic part used here) -/

/-- `c_{j,n} = 2^{hn + j + ⌈j/2⌉ - 1} 5^{2(a+b-c)n + j} z`, `z ∈ ℤ`
(Bai: `ν₂ ≥ hn + ⌊3j/2⌋ - 1`, `ν₅ ≥ 2(a+b-c)n + j`). -/
theorem cc_val (a b c n j : ℕ) (hc : Even c) (hcb : c < 2 * b) (hab : c ≤ a + b) (hn : 1 ≤ n)
    (hj : j ≤ c * n) : ∃ z : ℤ, cc a b c n j =
      2 ^ (h b c * n + j + (j + 1) / 2 - 1) * 5 ^ (2 * (a * n) + 2 * (b * n) - 2 * (c * n) + j) * z := by
  obtain ⟨h1, -⟩ := expo_facts a b c n hcb hab
  have hhn := h_mul_eq b c n hc hcb.le
  have hcn : c * n % 2 = 0 := Nat.even_iff.1 (hc.mul_right n)
  obtain ⟨z, hz⟩ := g_two_adic a b c n (c * n - j)
  refine ⟨z, ?_⟩
  have hKc := Kc_mul_ten a b c n hcb hab hn
  have hE : 4 * (b * n) - 2 * (c * n) - 1 + j + (b * n - (c * n - j) / 2) =
      h b c * n + j + (j + 1) / 2 - 1 := by omega
  unfold cc
  rw [hz, pow_succ]
  push_cast
  rw [← hE, show (10 : ℂ) ^ j = 2 ^ j * 5 ^ j by rw [← mul_pow]; norm_num]
  linear_combination ((2 : ℂ) ^ j * 5 ^ j * 2 ^ (b * n - (c * n - j) / 2) * z) * hKc

/-! ## Bai Lemma 2.6: the rational pole terms of `M_n J_n` are integers -/

theorem pole_term_isZ (a b c n m : ℕ) (hc : Even c) (hcb : c < 2 * b) (hab : c ≤ a + b)
    (hn : 1 ≤ n) (hm1 : 1 ≤ m) (hmN : m ≤ c * n) :
    IsZ (((M a b c n : ℝ) : ℂ) * I * (cc a b c n m / (m : ℂ) *
      ((((6 - 2 * I) ^ m)⁻¹ - ((4 + 2 * I) ^ m)⁻¹) - (((6 + 2 * I) ^ m)⁻¹ - ((4 - 2 * I) ^ m)⁻¹)))) := by
  obtain ⟨h1, h2⟩ := expo_facts a b c n hcb hab
  have hd0 := d0_mul a b c n hcb.le
  have hhn := h_mul_eq b c n hc hcb.le
  have hcn : c * n % 2 = 0 := Nat.even_iff.1 (hc.mul_right n)
  have e2an : 2 * a * n = 2 * (a * n) := by ring
  have hmd : m ≤ d0 a b c * n := by omega
  obtain ⟨K, hK⟩ := lcm_g_eq a b c n m hm1 hmd hmN
  obtain ⟨x, hx⟩ := X_int m
  obtain ⟨y, hy⟩ := Y_int m
  have hKc := Kc_mul_ten a b c n hcb hab hn
  obtain ⟨e2, he2⟩ : ∃ e, e = 4 * (b * n) - 2 * (c * n) - 1 := ⟨_, rfl⟩
  obtain ⟨e5, he5⟩ : ∃ e, e = 2 * (a * n) + 2 * (b * n) - 2 * (c * n) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ e, e = b * n - (c * n - m) / 2 := ⟨_, rfl⟩
  rw [← he2, ← he5] at hKc
  rw [← hv] at hK
  have hα : 4 + e2 + v = h b c * n + (4 + e2 + v - h b c * n) := by omega
  have hβ : 4 + e2 + v + m / 2 = h b c * n + m + (4 + e2 + v + m / 2 - h b c * n - m) := by omega
  have hα' : (2 : ℂ) ^ 4 * 2 ^ e2 * 2 ^ v = 2 ^ (h b c * n) * 2 ^ (4 + e2 + v - h b c * n) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← hα]
  have hβ' : (2 : ℂ) ^ 4 * 2 ^ e2 * 2 ^ v * 2 ^ (m / 2) =
      2 ^ (h b c * n) * 2 ^ m * 2 ^ (4 + e2 + v + m / 2 - h b c * n - m) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← hβ]
  have hK' : (Nat.lcmUpto (d0 a b c * n) : ℂ) * (g a b c n (c * n - m) : ℂ) =
      (Phi a b c n : ℂ) * m * (2 ^ v * K) := by
    have := congrArg (fun z : ℤ => (z : ℂ)) hK
    push_cast at this
    exact this
  have hP : (2 : ℂ) ^ (h b c * n) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hΦ : (Phi a b c n : ℂ) ≠ 0 := by exact_mod_cast (Phi_odd a b c n).pos.ne'
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hT : (10 : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hW : (2 : ℂ) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
  have h20 : (20 : ℂ) ^ m = 10 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
  refine ⟨5 ^ e5 * K * (2 ^ (4 + e2 + v - h b c * n) * x + 2 ^ (4 + e2 + v + m / 2 - h b c * n - m) * y), ?_⟩
  rw [M_cplx, bracket_eq, h20]
  unfold cc
  rw [pow_succ]
  calc 2 ^ 4 * (Nat.lcmUpto (d0 a b c * n) : ℂ) / (2 ^ (h b c * n) * (Phi a b c n : ℂ)) * I *
        (Kc a b c n * (10 ^ m * 10) * (g a b c n (c * n - m) : ℂ) / (m : ℂ) *
          (((2 + I) ^ m - (2 - I) ^ m) / 10 ^ m + ((3 + I) ^ m - (3 - I) ^ m) / (10 ^ m * 2 ^ m)))
      = (2 ^ 4 * (Kc a b c n * 10)) *
          ((Nat.lcmUpto (d0 a b c * n) : ℂ) * (g a b c n (c * n - m) : ℂ)) *
          (I * ((2 + I) ^ m - (2 - I) ^ m) * 2 ^ m + I * ((3 + I) ^ m - (3 - I) ^ m)) /
          (2 ^ (h b c * n) * (Phi a b c n : ℂ) * m * 2 ^ m) := by
        field_simp
        try ring
    _ = (2 ^ 4 * (2 ^ e2 * 5 ^ e5)) * ((Phi a b c n : ℂ) * m * (2 ^ v * K)) *
          (x * 2 ^ m + 2 ^ (m / 2) * y) / (2 ^ (h b c * n) * (Phi a b c n : ℂ) * m * 2 ^ m) := by
        rw [hKc, hK', hx, hy]
    _ = _ := by
        rw [div_eq_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero hP hΦ) hm0) hW)]
        push_cast
        linear_combination ((5 : ℂ) ^ e5 * (Phi a b c n : ℂ) * m * K * x * 2 ^ m) * hα' +
          ((5 : ℂ) ^ e5 * (Phi a b c n : ℂ) * m * K * y) * hβ'

/-! ## The `π`-coefficient -/

/-- `Φ_n 2^{bn - cn/2} ∣ g_{n,cn}`, and `M_n c_{0,n} / 2 = 4 lcm(1..d₀n) 5^{2(a+b-c)n} K`. -/
theorem V_term (a b c n : ℕ) (hc : Even c) (hcb : c < 2 * b) (hab : c ≤ a + b) (hn : 1 ≤ n) :
    ∃ K : ℤ, g a b c n (c * n) = (Phi a b c n : ℤ) * (2 ^ (b * n - c * n / 2) * K) ∧
      ((M a b c n : ℝ) : ℂ) * cc a b c n 0 / 2 =
        ((Nat.lcmUpto (d0 a b c * n) * 5 ^ (2 * (a * n) + 2 * (b * n) - 2 * (c * n)) * 4 * K : ℤ) : ℂ) := by
  obtain ⟨h1, h2⟩ := expo_facts a b c n hcb hab
  have hhn := h_mul_eq b c n hc hcb.le
  have hcn : c * n % 2 = 0 := Nat.even_iff.1 (hc.mul_right n)
  have hPhi : (Phi a b c n : ℤ) ∣ g a b c n (c * n) := by
    rw [Int.natCast_dvd]
    unfold Phi
    apply Finset.prod_primes_dvd
    · intro p hp; exact (mem_deletedPrimes hp).2.1.prime
    · intro p hp
      rw [← Int.natCast_dvd]
      have := deletion a b c n p hp 0 (dvd_zero _) (by positivity)
      rwa [sub_zero, Int.toNat_natCast] at this
  have h2g : (2 : ℤ) ^ (b * n - c * n / 2) ∣ g a b c n (c * n) := by
    have := g_two_adic a b c n (c * n)
    exact this
  obtain ⟨K, hK⟩ := ((two_coprime_Phi a b c n).pow_left.symm).mul_dvd hPhi h2g
  refine ⟨K, by rw [hK]; ring, ?_⟩
  have hKc := Kc_mul_ten a b c n hcb hab hn
  obtain ⟨e2, he2⟩ : ∃ e, e = 4 * (b * n) - 2 * (c * n) - 1 := ⟨_, rfl⟩
  obtain ⟨e5, he5⟩ : ∃ e, e = 2 * (a * n) + 2 * (b * n) - 2 * (c * n) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ e, e = b * n - c * n / 2 := ⟨_, rfl⟩
  rw [← he2, ← he5] at hKc
  rw [← hv] at hK
  rw [← he5]
  have hexp : (2 : ℂ) ^ 4 * 2 ^ e2 * 2 ^ v = 2 ^ (h b c * n) * 2 ^ 3 := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  have hG : (g a b c n (c * n) : ℂ) = (Phi a b c n : ℂ) * 2 ^ v * K := by
    have := congrArg (fun z : ℤ => (z : ℂ)) hK
    push_cast at this
    exact this
  have hP : (2 : ℂ) ^ (h b c * n) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hΦ : (Phi a b c n : ℂ) ≠ 0 := by exact_mod_cast (Phi_odd a b c n).pos.ne'
  rw [M_cplx]
  unfold cc
  rw [Nat.sub_zero, zero_add, pow_one, hG]
  calc 2 ^ 4 * (Nat.lcmUpto (d0 a b c * n) : ℂ) / (2 ^ (h b c * n) * (Phi a b c n : ℂ)) *
        (Kc a b c n * 10 * ((Phi a b c n : ℂ) * 2 ^ v * K)) / 2
      = (2 ^ 4 * (Kc a b c n * 10)) * (Nat.lcmUpto (d0 a b c * n) : ℂ) * ((Phi a b c n : ℂ) * 2 ^ v * K) /
          (2 ^ (h b c * n) * (Phi a b c n : ℂ) * 2) := by
        field_simp
    _ = _ := by
        rw [hKc, div_eq_iff (mul_ne_zero (mul_ne_zero hP hΦ) two_ne_zero)]
        push_cast
        linear_combination ((Nat.lcmUpto (d0 a b c * n) : ℂ) * 5 ^ e5 * (Phi a b c n : ℂ) * K) * hexp

end PiIrrationality.BaiGen
end

-- ===== inlined: scratch.research.campaign_pick.pi_stage3.PathFTC =====
section
set_option autoImplicit false

/-!
# The FTC step along the segment `t = -1 + s i`, `-2 ≤ s ≤ 2` (stage 3, private)

For a complex polynomial `P`, coefficients `c : ℕ → ℂ` and `N`, the function
`Fd(t) = P(t) + Σ_{j ≤ N} c_j [(5+t)^{-(j+1)} + (5-t)^{-(j+1)}]` has the primitive
`Fp(t) = ∫P + c_0 (log(5+t) - log(5-t)) + Σ_{j<N} c_{j+1}/(j+1) [(5-t)^{-(j+1)} - (5+t)^{-(j+1)}]`
on `{0 < re(5+t), 0 < re(5-t)}`, which contains the segment. Hence
`-∫_{-2}^{2} Fd(-1+si) ds = i (Fp(-1+2i) - Fp(-1-2i))`, and the logarithms contribute
`log(4+2i) - log(6-2i) - log(4-2i) + log(6+2i) = iπ/2` (`arg(20+20i) = π/4`).
-/

namespace PiIrrationality.BaiFTC

open Complex Polynomial PiIrrationality.PolyInt

/-- The partial-fraction shape `P(t) + Σ_{j ≤ N} c_j [(5+t)^{-(j+1)} + (5-t)^{-(j+1)}]`. -/
noncomputable def Fd (P : ℂ[X]) (c : ℕ → ℂ) (N : ℕ) : ℂ → ℂ := fun t =>
  P.eval t + ∑ j ∈ Finset.range (N + 1), c j * (((5 + t) ^ (j + 1))⁻¹ + ((5 - t) ^ (j + 1))⁻¹)

/-- Its primitive. -/
noncomputable def Fp (P : ℂ[X]) (c : ℕ → ℂ) (N : ℕ) : ℂ → ℂ := fun t =>
  (ant P).eval t + c 0 * (log (5 + t) - log (5 - t)) +
    ∑ j ∈ Finset.range N, c (j + 1) / ((j : ℂ) + 1) * (((5 - t) ^ (j + 1))⁻¹ - ((5 + t) ^ (j + 1))⁻¹)

theorem hasDerivAt_Fp (P : ℂ[X]) (c : ℕ → ℂ) (N : ℕ) (t : ℂ) (h1 : 0 < (5 + t).re)
    (h2 : 0 < (5 - t).re) : HasDerivAt (Fp P c N) (Fd P c N t) t := by
  have hp : (5 : ℂ) + t ≠ 0 := fun h => by rw [h] at h1; simp at h1
  have hm : (5 : ℂ) - t ≠ 0 := fun h => by rw [h] at h2; simp at h2
  have dA : HasDerivAt (fun t => (ant P).eval t) (P.eval t) t := by
    simpa [derivative_ant] using Polynomial.hasDerivAt (ant P) t
  have dp : HasDerivAt (fun t : ℂ => 5 + t) 1 t := (hasDerivAt_id' t).const_add 5
  have dm : HasDerivAt (fun t : ℂ => 5 - t) (-1) t := (hasDerivAt_id' t).const_sub 5
  have dL1 : HasDerivAt (fun t => log (5 + t)) (1 / (5 + t)) t :=
    dp.clog (mem_slitPlane_iff.2 (Or.inl h1))
  have dL2 : HasDerivAt (fun t => log (5 - t)) (-1 / (5 - t)) t :=
    dm.clog (mem_slitPlane_iff.2 (Or.inl h2))
  have hsum : HasDerivAt (fun t => ∑ j ∈ Finset.range N,
      c (j + 1) / ((j : ℂ) + 1) * (((5 - t) ^ (j + 1))⁻¹ - ((5 + t) ^ (j + 1))⁻¹))
      (∑ j ∈ Finset.range N, c (j + 1) * (((5 + t) ^ (j + 1 + 1))⁻¹ + ((5 - t) ^ (j + 1 + 1))⁻¹)) t := by
    apply HasDerivAt.fun_sum
    intro j _
    have hj : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have := (((dm.pow (j + 1)).inv (pow_ne_zero _ hm)).sub
      ((dp.pow (j + 1)).inv (pow_ne_zero _ hp))).const_mul (c (j + 1) / ((j : ℂ) + 1))
    refine this.congr_deriv ?_
    simp only [Pi.pow_apply, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have H := (dA.add ((dL1.sub dL2).const_mul (c 0))).add hsum
  refine H.congr_deriv ?_
  simp only [Fd]
  rw [Finset.sum_range_succ']
  simp only [zero_add, pow_one, one_div, neg_div, sub_neg_eq_add]
  ring

/-- Real-variable derivative of the segment. -/
theorem hasDerivAt_seg (s : ℝ) : HasDerivAt (fun s : ℝ => -1 + (s : ℂ) * I) I s := by
  have h := ((hasDerivAt_id s).ofReal_comp.mul_const I).const_add (-1 : ℂ)
  simpa using h

/-- **FTC along the segment.** -/
theorem neg_integral_eq (P : ℂ[X]) (c : ℕ → ℂ) (N : ℕ) (f : ℂ → ℂ)
    (hf : ∀ s : ℝ, f (-1 + (s : ℂ) * I) = Fd P c N (-1 + (s : ℂ) * I))
    (hcont : Continuous fun s : ℝ => f (-1 + (s : ℂ) * I)) :
    -∫ s in (-2 : ℝ)..2, f (-1 + (s : ℂ) * I) =
      I * (Fp P c N (-1 + 2 * I) - Fp P c N (-1 - 2 * I)) := by
  have hderiv : ∀ s ∈ Set.uIcc (-2 : ℝ) 2,
      HasDerivAt (fun s : ℝ => Fp P c N (-1 + (s : ℂ) * I)) (f (-1 + (s : ℂ) * I) * I) s := by
    intro s _
    have hre1 : 0 < (5 + (-1 + (s : ℂ) * I)).re := by simp
    have hre2 : 0 < (5 - (-1 + (s : ℂ) * I)).re := by simp; norm_num
    rw [hf]
    exact (hasDerivAt_Fp P c N _ hre1 hre2).comp s (hasDerivAt_seg s)
  have hint : IntervalIntegrable (fun s : ℝ => f (-1 + (s : ℂ) * I) * I) MeasureTheory.volume (-2) 2 :=
    (hcont.mul continuous_const).intervalIntegrable _ _
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_mul_const] at key
  rw [show (-1 : ℂ) + ((2 : ℝ) : ℂ) * I = -1 + 2 * I by push_cast; ring,
    show (-1 : ℂ) + ((-2 : ℝ) : ℂ) * I = -1 - 2 * I by push_cast; ring] at key
  linear_combination I * key - (∫ s in (-2 : ℝ)..2, f (-1 + (s : ℂ) * I)) * I_mul_I

/-- `arg(20 + 20i) = π/4`. -/
theorem arg_twenty : arg (20 + 20 * I) = Real.pi / 4 := by
  have h2 : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have e : (20 + 20 * I : ℂ) = ((20 * √2 : ℝ) : ℂ) *
      (cos ((Real.pi / 4 : ℝ) : ℂ) + sin ((Real.pi / 4 : ℝ) : ℂ) * I) := by
    rw [← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast
    linear_combination (-10 * (1 + I)) * h2
  rw [e, arg_real_mul _ (by positivity),
    arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩]

theorem arg_sum_mem {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    x.arg + y.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
  have h1 := abs_lt.1 (abs_arg_lt_pi_div_two_iff.2 (Or.inl hx))
  have h2 := abs_lt.1 (abs_arg_lt_pi_div_two_iff.2 (Or.inl hy))
  constructor <;> linarith [Real.pi_pos]

/-- The logarithmic bracket: `log(4+2i) - log(6-2i) - (log(4-2i) - log(6+2i)) = (π/2) i`. -/
theorem log_bracket :
    log (4 + 2 * I) - log (6 - 2 * I) - (log (4 - 2 * I) - log (6 + 2 * I)) = (Real.pi / 2 : ℝ) * I := by
  have nz : ∀ z : ℂ, 0 < z.re → z ≠ 0 := fun z hz h => by rw [h] at hz; simp at hz
  have m1 : log (4 + 2 * I) + log (6 + 2 * I) = log (20 + 20 * I) := by
    rw [← log_mul (nz _ (by norm_num)) (nz _ (by norm_num)) (arg_sum_mem (by norm_num) (by norm_num))]
    congr 1; ring_nf; rw [I_sq]; ring
  have m2 : log (4 - 2 * I) + log (6 - 2 * I) = log (20 - 20 * I) := by
    rw [← log_mul (nz _ (by norm_num)) (nz _ (by norm_num)) (arg_sum_mem (by norm_num) (by norm_num))]
    congr 1; ring_nf; rw [I_sq]; ring
  have hc : (20 - 20 * I : ℂ) = (starRingEnd ℂ) (20 + 20 * I) := by
    apply Complex.ext <;> simp
  have hlc : log (20 - 20 * I) = (starRingEnd ℂ) (log (20 + 20 * I)) := by
    rw [hc, log_conj]
    rw [arg_twenty]
    intro h
    linarith [Real.pi_pos]
  have him : log (20 + 20 * I) - (starRingEnd ℂ) (log (20 + 20 * I)) =
      2 * ((log (20 + 20 * I)).im : ℂ) * I := by
    apply Complex.ext <;> simp <;> ring
  rw [log_im, arg_twenty] at him
  calc log (4 + 2 * I) - log (6 - 2 * I) - (log (4 - 2 * I) - log (6 + 2 * I))
      = (log (4 + 2 * I) + log (6 + 2 * I)) - (log (4 - 2 * I) + log (6 - 2 * I)) := by ring
    _ = _ := by
      rw [m1, m2, hlc, him]; push_cast; ring

/-- The primitive's increment: the polynomial part, `c₀ (π/2) i`, and the rational pole terms. -/
theorem Fp_sub (P : ℂ[X]) (c : ℕ → ℂ) (N : ℕ) :
    Fp P c N (-1 + 2 * I) - Fp P c N (-1 - 2 * I) =
      Lam P (-1 - 2 * I) (-1 + 2 * I) + c 0 * ((Real.pi / 2 : ℝ) * I) +
        ∑ j ∈ Finset.range N, c (j + 1) / ((j : ℂ) + 1) *
          ((((6 - 2 * I) ^ (j + 1))⁻¹ - ((4 + 2 * I) ^ (j + 1))⁻¹) -
            (((6 + 2 * I) ^ (j + 1))⁻¹ - ((4 - 2 * I) ^ (j + 1))⁻¹)) := by
  have e1 : (5 : ℂ) + (-1 + 2 * I) = 4 + 2 * I := by ring
  have e2 : (5 : ℂ) - (-1 + 2 * I) = 6 - 2 * I := by ring
  have e3 : (5 : ℂ) + (-1 - 2 * I) = 4 - 2 * I := by ring
  have e4 : (5 : ℂ) - (-1 - 2 * I) = 6 + 2 * I := by ring
  rw [← log_bracket]
  simp only [Fp, Lam, e1, e2, e3, e4]
  have hS : ∑ j ∈ Finset.range N, c (j + 1) / ((j : ℂ) + 1) *
          ((((6 - 2 * I) ^ (j + 1))⁻¹ - ((4 + 2 * I) ^ (j + 1))⁻¹) -
            (((6 + 2 * I) ^ (j + 1))⁻¹ - ((4 - 2 * I) ^ (j + 1))⁻¹)) =
      ∑ j ∈ Finset.range N, c (j + 1) / ((j : ℂ) + 1) *
          (((6 - 2 * I) ^ (j + 1))⁻¹ - ((4 + 2 * I) ^ (j + 1))⁻¹) -
      ∑ j ∈ Finset.range N, c (j + 1) / ((j : ℂ) + 1) *
          (((6 + 2 * I) ^ (j + 1))⁻¹ - ((4 - 2 * I) ^ (j + 1))⁻¹) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hS]
  ring

end PiIrrationality.BaiFTC
end

-- ===== inlined: scratch.research.campaign_pick.pi_stage3.Bridge =====
section
set_option autoImplicit false

/-!
# The residue bridge `g_{n,cn} = (-1)^{cn} coef_n` (stage 3, private)

Substituting `w = -z/(1-z)` turns `[w^N] H(w)(1-w)^{-(N+1)}` into
`(-1)^N [z^N] A(z)^n (1-z)^{-d₀n}`. Algebraically: `A^n(z) = Σ_i h_i (-1)^i z^i (1-z)^{E-i}`
(`E = 2an + 4bn = d₀n + 2N`), and `(1-z)^{E-i} (1-z)^{-d₀n} = (1-z)^{2N-i}` for `i ≤ N`.
-/

namespace PiIrrationality.BaiGen

open Polynomial

theorem coeff_one_sub_X_pow (m k : ℕ) :
    (((1 : ℤ[X]) - X) ^ m).coeff k = (-1) ^ k * (m.choose k : ℤ) := by
  induction m generalizing k with
  | zero => rcases k with _ | k <;> simp [coeff_one]
  | succ m ih =>
    rw [pow_succ, mul_sub, mul_one, coeff_sub]
    rcases k with _ | k
    · simp [ih]
    · rw [coeff_mul_X, ih, ih, Nat.choose_succ_succ']; push_cast; ring

theorem d0_mul' (a b c n : ℕ) (hcb : c ≤ 2 * b) :
    d0 a b c * n + 2 * (c * n) = 2 * a * n + 4 * (b * n) := by
  have e1 : (2 * a + 4 * b) * n = 2 * a * n + 4 * (b * n) := by ring
  have e2 : 2 * c * n = 2 * (c * n) := by ring
  have hle : 2 * c * n ≤ (2 * a + 4 * b) * n := Nat.mul_le_mul_right _ (by omega)
  unfold d0
  rw [Nat.sub_mul]
  omega

/-- `A^n(z) = Σ_{i ≤ E} h_i (-1)^i z^i (1-z)^{E-i}`, `E = 2an + 4bn`. -/
theorem A_pow_eq (a b n : ℕ) :
    (A a b ^ n).map (Nat.castRingHom ℤ) =
      ∑ i ∈ Finset.range (2 * a * n + 4 * (b * n) + 1),
        C ((Hw a b n).coeff i * (-1) ^ i) * X ^ i * (1 - X) ^ (2 * a * n + 4 * (b * n) - i) := by
  set E := 2 * a * n + 4 * (b * n) with hE
  apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := ({1}ᶜ : Set ℚ))
  · intro q hq
    have hq1 : (1 : ℚ) - q ≠ 0 := sub_ne_zero.2 (Ne.symm (Set.mem_compl_singleton_iff.mp hq))
    simp only [Set.mem_ofPred_eq]
    set w : ℚ := -q / (1 - q) with hw
    have hdeg : ((Hw a b n).map (Int.castRingHom ℚ)).natDegree < E + 1 := by
      have := PiIrrationality.BaiPF.natDegree_Hw_le a b n
      have h2 := natDegree_map_le (f := Int.castRingHom ℚ) (p := Hw a b n)
      omega
    have hsum : ((Hw a b n).map (Int.castRingHom ℚ)).eval w =
        ∑ i ∈ Finset.range (E + 1), ((Hw a b n).coeff i : ℚ) * w ^ i := by
      rw [eval_eq_sum_range' hdeg]
      simp [coeff_map]
    have hHw : ((Hw a b n).map (Int.castRingHom ℚ)).eval w =
        (2 * w - 1) ^ (2 * a * n) * (25 * w ^ 4 - 50 * w ^ 3 + 39 * w ^ 2 - 14 * w + 2) ^ (b * n) := by
      simp [Hw, Qw]
    have h1 : (1 - q) * (2 * w - 1) = -(1 + q) := by rw [hw]; field_simp; ring
    have h2 : (1 - q) ^ 4 * (25 * w ^ 4 - 50 * w ^ 3 + 39 * w ^ 2 - 14 * w + 2) =
        2 + 6 * q + 9 * q ^ 2 + 6 * q ^ 3 + 2 * q ^ 4 := by rw [hw]; field_simp; ring
    have hL : Polynomial.eval q (((A a b ^ n).map (Nat.castRingHom ℤ)).map (Int.castRingHom ℚ)) =
        (1 + q) ^ (2 * a * n) * (2 + 6 * q + 9 * q ^ 2 + 6 * q ^ 3 + 2 * q ^ 4) ^ (b * n) := by
      simp [A]
      rw [mul_pow, ← pow_mul, ← pow_mul]
    have hR : Polynomial.eval q ((∑ i ∈ Finset.range (E + 1),
        C ((Hw a b n).coeff i * (-1) ^ i) * X ^ i * (1 - X) ^ (E - i) : ℤ[X]).map (Int.castRingHom ℚ)) =
        (1 - q) ^ E * ((Hw a b n).map (Int.castRingHom ℚ)).eval w := by
      rw [hsum, Finset.mul_sum, Polynomial.map_sum, eval_finsetSum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
        Polynomial.map_sub, Polynomial.map_one, eval_mul, eval_pow, eval_C, eval_X, eval_sub, eval_one]
      simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
      have hsplit : (1 - q) ^ E = (1 - q) ^ (E - i) * (1 - q) ^ i := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]
      have hwi : (1 - q) ^ i * w ^ i = (-1) ^ i * q ^ i := by
        rw [← mul_pow, hw, mul_div_cancel₀ _ hq1, neg_pow]
      rw [hsplit]
      linear_combination (-(((Hw a b n).coeff i : ℚ)) * (1 - q) ^ (E - i)) * hwi
    rw [hL, hR, hHw]
    have hEsplit : (1 - q) ^ E = (1 - q) ^ (2 * a * n) * ((1 - q) ^ 4) ^ (b * n) := by
      rw [hE, ← pow_mul, ← pow_add]
    rw [hEsplit]
    calc (1 + q) ^ (2 * a * n) * (2 + 6 * q + 9 * q ^ 2 + 6 * q ^ 3 + 2 * q ^ 4) ^ (b * n)
        = (-(1 + q)) ^ (2 * a * n) * (2 + 6 * q + 9 * q ^ 2 + 6 * q ^ 3 + 2 * q ^ 4) ^ (b * n) := by
          rw [Even.neg_pow ⟨a * n, by ring⟩]
      _ = ((1 - q) * (2 * w - 1)) ^ (2 * a * n) *
            ((1 - q) ^ 4 * (25 * w ^ 4 - 50 * w ^ 3 + 39 * w ^ 2 - 14 * w + 2)) ^ (b * n) := by
          rw [h1, h2]
      _ = _ := by rw [mul_pow, mul_pow]; ring
  · exact (Set.finite_singleton (1 : ℚ)).infinite_compl

/-- `coef_n = [z^{cn}] A^n(z) (1-z)^{-d₀n}`. -/
theorem coef_eq_coeff (a b c n : ℕ) (hD : 0 < d0 a b c * n) :
    (coef a b c n : ℤ) = PowerSeries.coeff (c * n)
      ((((A a b ^ n).map (Nat.castRingHom ℤ) : ℤ[X]) : PowerSeries ℤ) *
        (PowerSeries.invOneSubPow ℤ (d0 a b c * n)).val) := by
  rw [PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos _ _ hD, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  unfold coef
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.coeff_map, PowerSeries.coeff_mk, Nat.choose_symm_add]
  simp

/-- `g_{n,N} = Σ_{i ≤ N} h_i C(2N-i, N)`. -/
theorem g_eq_sum (a b c n : ℕ) : g a b c n (c * n) =
    ∑ i ∈ Finset.range (c * n + 1), (Hw a b n).coeff i * ((2 * (c * n) - i).choose (c * n) : ℤ) := by
  unfold g Gw
  rw [PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos _ _ (Nat.succ_pos _),
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [Polynomial.coeff_coe, PowerSeries.coeff_mk]
  congr 2
  rw [show c * n + 1 - 1 + (c * n - i) = 2 * (c * n) - i by omega,
    show c * n + 1 - 1 = c * n by omega]

/-- One term of the transformed sum. -/
theorem coeff_term (r : ℤ) (i N D E : ℕ) (hE : E = D + 2 * N) :
    PowerSeries.coeff N ((((C r * X ^ i * (1 - X) ^ (E - i) : ℤ[X])) : PowerSeries ℤ) *
      (PowerSeries.invOneSubPow ℤ D).val) =
      if i ≤ N then r * ((-1) ^ (N - i) * ((2 * N - i).choose N : ℤ)) else 0 := by
  rw [Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, mul_assoc,
    mul_assoc, Polynomial.coe_C, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  split_ifs with hi
  · have hEi : E - i = (2 * N - i) + D := by omega
    rw [hEi, Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X,
      PowerSeries.one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow, ← Polynomial.coe_X,
      ← Polynomial.coe_one, ← Polynomial.coe_sub, ← Polynomial.coe_pow, Polynomial.coeff_coe,
      coeff_one_sub_X_pow, Nat.choose_symm_of_eq_add (show 2 * N - i = (N - i) + N by omega)]
  · rw [mul_zero]

/-- **The residue bridge** `g_{n,cn} = (-1)^{cn} coef_n` (`w = -z/(1-z)`). -/
theorem g_cn_eq_coef (a b c n : ℕ) (hcb : c ≤ 2 * b) (hD : 0 < d0 a b c * n) :
    g a b c n (c * n) = (-1) ^ (c * n) * (coef a b c n : ℤ) := by
  have hE := d0_mul' a b c n hcb
  have key : (coef a b c n : ℤ) = (-1) ^ (c * n) * g a b c n (c * n) := by
    rw [coef_eq_coeff a b c n hD, A_pow_eq, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum,
      Finset.sum_mul, map_sum, g_eq_sum, Finset.mul_sum]
    simp only [Polynomial.coeToPowerSeries.ringHom_apply]
    rw [← Finset.sum_subset (Finset.range_subset_range.2 (show c * n + 1 ≤ 2 * a * n + 4 * (b * n) + 1 by omega))]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [coeff_term _ i (c * n) (d0 a b c * n) _ hE.symm, if_pos (by omega)]
      have hs : ((-1 : ℤ) ^ i) * (-1) ^ (c * n - i) = (-1) ^ (c * n) := by
        rw [← pow_add, Nat.add_sub_cancel' (by omega)]
      linear_combination ((Hw a b n).coeff i * ((2 * (c * n) - i).choose (c * n) : ℤ)) * hs
    · intro i _ hi
      rw [Finset.mem_range] at hi
      rw [coeff_term _ i (c * n) (d0 a b c * n) _ hE.symm, if_neg (by omega)]
  rw [key, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

end PiIrrationality.BaiGen

namespace PiIrrationality.Bai

/-- **`g_{n,5570n} = coef_n`** at Bai's exponents (`5570n` is even). -/
theorem g_eq_coef (n : ℕ) (hn : 1 ≤ n) : g n (5570 * n) = (coef n : ℤ) := by
  have h := BaiGen.g_cn_eq_coef 1857 3714 5570 n (by norm_num) (by rw [d0_eq]; omega)
  rw [g, h, coef_eq, Even.neg_one_pow ⟨2785 * n, by ring⟩, one_mul]

end PiIrrationality.Bai
end

-- ===== inlined: scratch.research.campaign_pick.pi_stage3.LinearForm =====
section
set_option autoImplicit false

/-!
# Bai's Proposition 2.7: `M_n J_n = U_n + V_n π` (stage 3, private)

* `R_eq_Fd` (partial fractions): `R_n(t) = P_n(t) + Σ_{j ≤ cn} c_{j,n} [(5+t)^{-(j+1)} + (5-t)^{-(j+1)}]`
  for `t ≠ ±5`, from `pf_identity` in `w = (t+5)/10` and `Pt_map`.
* `J_formula` (FTC): `J_n = i (F(-1+2i) - F(-1-2i))` with the primitive `Fp` of `PathFTC`.
* `linearForm_gen`: for variable `(a, b, c)` with `c` even, `c < 2b`, `c ≤ a + b`, `n ≥ 1`:
  `M_n J_n = U + V π`, `U, V ∈ ℤ`, `V = -M_n 2^{(4b-2c)n} 5^{2(a+b-c)n} coef_n / 4`.
* `Bai.linearForm`: the specialisation `(1857, 3714, 5570)`, `V = -(1/4) M_n 25^n 2^{3716n} coef_n`.
-/

namespace PiIrrationality.BaiGen

open Complex Polynomial PiIrrationality.PolyInt PiIrrationality.BaiPF PiIrrationality.BaiFTC

/-- Reflection of a truncated power sum: `(Σ_{i ≤ N} G_i x^i) / x^{N+1} = Σ_{j ≤ N} G_{N-j} x^{-(j+1)}`. -/
theorem refl_sum (G : ℕ → ℂ) (x : ℂ) (hx : x ≠ 0) (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), G i * x ^ i) / x ^ (N + 1) =
      ∑ j ∈ Finset.range (N + 1), G (N - j) * (x ^ (j + 1))⁻¹ := by
  rw [Finset.sum_div, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [show N + 1 - 1 - j = N - j by omega]
  have : x ^ (N + 1) = x ^ (N - j) * x ^ (j + 1) := by rw [← pow_add]; congr 1; omega
  rw [this]
  field_simp

/-- **Partial fractions** (Bai §2): `R_n(t) = P_n(t) + Σ_{j=0}^{cn} c_{j,n} [(5+t)^{-(j+1)} + (5-t)^{-(j+1)}]`. -/
theorem R_eq_Fd (a b c n : ℕ) (t : ℂ) (hp : 5 + t ≠ 0) (hm : 5 - t ≠ 0) :
    R a b c n t = Fd ((Pt a b c n).map (Int.castRingHom ℂ)) (cc a b c n) (c * n) t := by
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = 1 / 10 * t + 1 / 2 := ⟨_, rfl⟩
  have hw5 : 5 + t = 10 * w := by rw [hw]; ring
  have hw5' : 5 - t = 10 * (1 - w) := by rw [hw]; ring
  have hw0 : w ≠ 0 := fun h => hp (by rw [hw5, h, mul_zero])
  have h1w0 : 1 - w ≠ 0 := fun h => hm (by rw [hw5', h, mul_zero])
  have hPt := congrArg (Polynomial.eval t) (Pt_map a b c n)
  simp only [eval_mul, eval_C, eval_comp, sigt, eval_add, eval_X] at hPt
  rw [← hw] at hPt
  have hpf := congrArg (fun p : ℤ[X] => (p.map (Int.castRingHom ℂ)).eval w)
    (pf_identity (Hw a b n) (c * n) (Hw_comp a b n))
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sub, Polynomial.map_one, eval_add, eval_mul, eval_pow, eval_X, eval_sub,
    eval_one] at hpf
  have hT : ∀ x : ℂ, ((T (Hw a b n) (c * n)).map (Int.castRingHom ℂ)).eval x =
      ∑ i ∈ Finset.range (c * n + 1), (g a b c n i : ℂ) * x ^ i := by
    intro x
    simp [T, Polynomial.map_sum, eval_finsetSum, gc_eq]
  have hRem : ((Rem (Hw a b n) (c * n)).map (Int.castRingHom ℂ)).eval w =
      (1 - w) ^ (c * n + 1) * ∑ i ∈ Finset.range (c * n + 1), (g a b c n i : ℂ) * w ^ i +
        w ^ (c * n + 1) * ∑ i ∈ Finset.range (c * n + 1), (g a b c n i : ℂ) * (1 - w) ^ i := by
    simp only [Rem, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_one, Polynomial.map_X, eval_add, eval_mul, eval_pow, eval_sub, eval_one, eval_X,
      Polynomial.map_comp, eval_comp]
    rw [hT, hT]
  have hHw : ((Hw a b n).map (Int.castRingHom ℂ)).eval w =
      (2 * w - 1) ^ (2 * a * n) * (25 * w ^ 4 - 50 * w ^ 3 + 39 * w ^ 2 - 14 * w + 2) ^ (b * n) := by
    simp [Hw, Qw]
  have hnum : 5 * t ^ (2 * a * n) * (t ^ 4 + 6 * t ^ 2 + 25) ^ (b * n) =
      Kc a b c n * 100 ^ (c * n + 1) * ((Hw a b n).map (Int.castRingHom ℂ)).eval w := by
    rw [hHw]
    have h2w : 2 * w - 1 = t / 5 := by rw [hw]; ring
    have hq : 25 * w ^ 4 - 50 * w ^ 3 + 39 * w ^ 2 - 14 * w + 2 = (t ^ 4 + 6 * t ^ 2 + 25) / 400 := by
      rw [hw]; ring
    rw [h2w, hq, div_pow, div_pow, Kc]
    field_simp
    ring
  have hden : (25 - t ^ 2) ^ (c * n + 1) = 100 ^ (c * n + 1) * (w ^ (c * n + 1) * (1 - w) ^ (c * n + 1)) := by
    rw [← mul_pow, ← mul_pow]; congr 1; rw [hw]; ring
  have hA : w ^ (c * n + 1) ≠ 0 := pow_ne_zero _ hw0
  have hB : (1 - w) ^ (c * n + 1) ≠ 0 := pow_ne_zero _ h1w0
  have h100 : (100 : ℂ) ^ (c * n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hR : R a b c n t = Kc a b c n * ((Qp (Hw a b n) (c * n)).map (Int.castRingHom ℂ)).eval w +
      Kc a b c n * ((∑ i ∈ Finset.range (c * n + 1), (g a b c n i : ℂ) * w ^ i) / w ^ (c * n + 1)) +
      Kc a b c n * ((∑ i ∈ Finset.range (c * n + 1), (g a b c n i : ℂ) * (1 - w) ^ i) /
        (1 - w) ^ (c * n + 1)) := by
    unfold R
    rw [hnum, hden, hpf, hRem, mul_pow]
    field_simp
    ring
  rw [hR, refl_sum _ w hw0, refl_sum _ (1 - w) h1w0]
  simp only [Fd, hPt]
  rw [Finset.mul_sum, Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  unfold cc
  rw [hw5, hw5', mul_pow, mul_pow]
  have h10 : (10 : ℂ) ^ (j + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hwj : w ^ (j + 1) ≠ 0 := pow_ne_zero _ hw0
  have hwj' : (1 - w) ^ (j + 1) ≠ 0 := pow_ne_zero _ h1w0
  field_simp

theorem seg_re (s : ℝ) : 0 < ((5 : ℂ) + (-1 + (s : ℂ) * I)).re ∧ 0 < ((5 : ℂ) - (-1 + (s : ℂ) * I)).re := by
  constructor <;> simp <;> norm_num

theorem ne_zero_of_re_pos {z : ℂ} (h : 0 < z.re) : z ≠ 0 := fun h' => by rw [h'] at h; simp at h

theorem R_seg_cont (a b c n : ℕ) : Continuous fun s : ℝ => R a b c n (-1 + (s : ℂ) * I) := by
  have hden : ∀ s : ℝ, (25 - (-1 + (s : ℂ) * I) ^ 2) ^ (c * n + 1) ≠ 0 := by
    intro s
    apply pow_ne_zero
    apply ne_zero_of_re_pos
    simp [sq]
    nlinarith [sq_nonneg s]
  unfold R
  exact Continuous.div (by fun_prop) (by fun_prop) hden

/-- **FTC**: `J_n = i (F(-1+2i) - F(-1-2i))`. -/
theorem J_formula (a b c n : ℕ) :
    J a b c n = I * (Fp ((Pt a b c n).map (Int.castRingHom ℂ)) (cc a b c n) (c * n) (-1 + 2 * I) -
      Fp ((Pt a b c n).map (Int.castRingHom ℂ)) (cc a b c n) (c * n) (-1 - 2 * I)) := by
  unfold J
  exact neg_integral_eq _ _ _ (R a b c n)
    (fun s => R_eq_Fd a b c n _ (ne_zero_of_re_pos (seg_re s).1) (ne_zero_of_re_pos (seg_re s).2))
    (R_seg_cont a b c n)

/-- **Bai Proposition 2.7, variable exponents.** -/
theorem linearForm_gen (a b c n : ℕ) (hc : Even c) (hcb : c < 2 * b) (hab : c ≤ a + b) (hn : 1 ≤ n) :
    ∃ U V : ℤ, ((M a b c n : ℝ) : ℂ) * J a b c n = (U : ℂ) + (V : ℂ) * (Real.pi : ℂ) ∧
      (V : ℝ) = -(M a b c n * 2 ^ (4 * (b * n) - 2 * (c * n)) *
        5 ^ (2 * (a * n) + 2 * (b * n) - 2 * (c * n)) * (coef a b c n : ℝ) / 4) := by
  obtain ⟨z1, hz1⟩ := Ypoly_int a b c n hc hcb.le
  obtain ⟨K, hgK, hVK⟩ := V_term a b c n hc hcb hab hn
  have hpole : ∀ j ∈ Finset.range (c * n), IsZ (((M a b c n : ℝ) : ℂ) * I *
      (cc a b c n (j + 1) / ((j : ℂ) + 1) *
        ((((6 - 2 * I) ^ (j + 1))⁻¹ - ((4 + 2 * I) ^ (j + 1))⁻¹) -
          (((6 + 2 * I) ^ (j + 1))⁻¹ - ((4 - 2 * I) ^ (j + 1))⁻¹)))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have := pole_term_isZ a b c n (j + 1) hc hcb hab hn (by omega) (by omega)
    push_cast at this
    exact this
  obtain ⟨z2, hz2⟩ := IsZ_sum _ _ hpole
  refine ⟨8 * z1 + z2, -(Nat.lcmUpto (d0 a b c * n) * 5 ^ (2 * (a * n) + 2 * (b * n) - 2 * (c * n)) * 4 * K), ?_, ?_⟩
  · rw [J_formula, Fp_sub]
    have hL : ((M a b c n : ℝ) : ℂ) * (I * Lam ((Pt a b c n).map (Int.castRingHom ℂ)) (-1 - 2 * I) (-1 + 2 * I)) =
        8 * z1 := by
      rw [← hz1, M_cplx]; unfold Ypoly; ring
    have hS : ((M a b c n : ℝ) : ℂ) * (I * ∑ j ∈ Finset.range (c * n), cc a b c n (j + 1) / ((j : ℂ) + 1) *
        ((((6 - 2 * I) ^ (j + 1))⁻¹ - ((4 + 2 * I) ^ (j + 1))⁻¹) -
          (((6 + 2 * I) ^ (j + 1))⁻¹ - ((4 - 2 * I) ^ (j + 1))⁻¹))) = z2 := by
      rw [← hz2, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    push_cast at hVK ⊢
    linear_combination hL + hS - (Real.pi : ℂ) * hVK +
      (((M a b c n : ℝ) : ℂ) * cc a b c n 0 * (Real.pi : ℂ) / 2) * I_mul_I
  · have hN : Even (c * n) := hc.mul_right n
    have hD : 0 < d0 a b c * n := by
      have := d0_mul a b c n hcb.le
      have := (expo_facts a b c n hcb hab).1
      omega
    have hcoef : (coef a b c n : ℤ) = g a b c n (c * n) := by
      rw [g_cn_eq_coef a b c n hcb.le hD, hN.neg_one_pow, one_mul]
    have hcoefR : (coef a b c n : ℝ) =
        (Phi a b c n : ℝ) * (2 ^ (b * n - c * n / 2) * K) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) (hcoef.trans hgK)
      push_cast at this
      exact this
    have hhn := h_mul_eq b c n hc hcb.le
    have hcn : c * n % 2 = 0 := Nat.even_iff.1 hN
    have h1 := (expo_facts a b c n hcb hab).1
    have hexp : (2 : ℝ) ^ (4 * (b * n) - 2 * (c * n)) * 2 ^ (b * n - c * n / 2) = 2 ^ (h b c * n) := by
      rw [← pow_add]; congr 1; omega
    have hexp' : (2 : ℝ) ^ (4 * (b * n) - 2 * (c * n)) = 2 ^ (h b c * n) / 2 ^ (b * n - c * n / 2) :=
      eq_div_of_mul_eq (pow_ne_zero _ two_ne_zero) hexp
    have hΦ : (Phi a b c n : ℝ) ≠ 0 := by exact_mod_cast (Phi_odd a b c n).pos.ne'
    unfold M
    rw [hcoefR, hexp']
    push_cast
    field_simp
    ring

end PiIrrationality.BaiGen

namespace PiIrrationality.BaiFTC

open Complex Polynomial PiIrrationality.PolyInt

/-- **FTC for a polynomial** along the segment: `-∫_{-2}^{2} S(-1+si) ds = i ∫_{-1-2i}^{-1+2i} S`. -/
theorem neg_integral_poly (S : ℂ[X]) :
    -∫ s in (-2 : ℝ)..2, S.eval (-1 + (s : ℂ) * I) = I * Lam S (-1 - 2 * I) (-1 + 2 * I) := by
  have h := neg_integral_eq S (fun _ => 0) 0 (fun t => S.eval t)
    (fun s => by simp [Fd])
    (S.differentiable.continuous.comp (by fun_prop : Continuous fun s : ℝ => -1 + (s : ℂ) * I))
  rw [h, Fp_sub]
  simp

end PiIrrationality.BaiFTC

namespace PiIrrationality.Bai

open Complex

/-- **Bai Proposition 2.7** at `(a,b,c) = (1857, 3714, 5570)`:
`M_n J_n = U_n + V_n π` with `U_n, V_n ∈ ℤ` and `V_n = -(1/4) M_n 25^n 2^{3716n} coef_n`. -/
theorem linearForm_main (n : ℕ) (hn : 1 ≤ n) :
    ∃ U V : ℤ, (M n : ℂ) * J n = (U : ℂ) + (V : ℂ) * (Real.pi : ℂ) ∧
      (V : ℝ) = -(M n * 25 ^ n * 2 ^ (3716 * n) * (coef n : ℝ) / 4) := by
  obtain ⟨U, V, h1, h2⟩ := BaiGen.linearForm_gen 1857 3714 5570 n ⟨2785, by norm_num⟩ (by norm_num)
    (by norm_num) hn
  refine ⟨U, V, ?_, ?_⟩
  · rw [M_eq, J_eq]; exact h1
  · rw [M_eq, coef_eq, h2,
      show 4 * (3714 * n) - 2 * (5570 * n) = 3716 * n by omega,
      show 2 * (1857 * n) + 2 * (3714 * n) - 2 * (5570 * n) = 2 * n by omega,
      show (5 : ℝ) ^ (2 * n) = 25 ^ n by rw [pow_mul]; norm_num]
    ring

end PiIrrationality.Bai
end

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ U V : ℤ, (PiIrrationality.Bai.M n : ℂ) * PiIrrationality.Bai.J n =
        (U : ℂ) + (V : ℂ) * (Real.pi : ℂ) ∧
      (V : ℝ) = -(PiIrrationality.Bai.M n * 25 ^ n * 2 ^ (3716 * n) *
        (PiIrrationality.Bai.coef n : ℝ) / 4) := by
  exact PiIrrationality.Bai.linearForm_main n hn
