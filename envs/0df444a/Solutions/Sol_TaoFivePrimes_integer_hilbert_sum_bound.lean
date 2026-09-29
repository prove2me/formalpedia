-- Prove2me | solution 1 for TaoFivePrimes.integer_hilbert_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-12T16:50:52.142665+00:00
-- url     : https://prove2.me/submissions/ebc80926-623c-4483-aa9f-2178d3505ef9

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Matrix.Spectrum
section
-- Adapted only by renaming the final theorem from accepted Prove2Me submission
-- e2c521f7-2d40-47aa-84b0-cd6cdb3872a6 (Mathlib 0df444a360eaa60ab8c11dca51a86af692955474).
-- Original: anthropics/zeta-23-lean, commit 182afbf851aa42a8ae78507be83f2356d3a33260.
-- License copy: missions/five-primes/third-party/Apache-2.0.txt.

-- from Zeta23.MV.EigenIdentity
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The Preissmann–Lévêque eigen-identity (arXiv:2203.14950 Lemma 2.1)

For real `c_r > 0`, injective real `freq`, complex `u` and real `μ` with the eigen-relation
`Σ_{n≠m} c_m c_n u_n/(freq m − freq n) = iμ u_m` for every `m`, we prove, for every `m`,

  `μ² |u_m|² = Σ_{n≠m} c_m² c_n² |u_n|²/(freq m − freq n)²
               + 2 Σ_{n≠m} c_m³ c_n Re(u_m ū_n)/(freq m − freq n)²`.

Proof (pure finite algebra): expand `|iμ u_m|²` as a double sum over `(n,p)`; the diagonal
`p = n` is the first term; off the diagonal use the partial fraction
`1/((λm−λn)(λm−λp)) = 1/((λm−λn)(λn−λp)) − 1/((λm−λp)(λn−λp))` to write the summand as
`G(n,p) + G(p,n)`, so the off-diagonal part is `2 Σ_n Σ_{p≠n,m} G(n,p)`; the inner sum is
`Re(u_n · W_n)` with `W_n = Σ_{p≠n,m} c_p ū_p/(λn−λp)`, and the conjugate eigen-relation at `n`
gives `W_n = −iμ ū_n/c_n − c_m ū_m/(λn−λm)`; the `−iμ|u_n|²/c_n` piece is purely imaginary and
dies under `Re` — the Montgomery–Vaughan cancellation — leaving the second term.
-/

noncomputable section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Zeta23
namespace MV

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {freq : ι → ℝ}

/-- `‖z‖² = Re(z z̄)`. -/
lemma norm_sq_eq_re_mul_conj (z : ℂ) : ‖z‖ ^ 2 = (z * conj z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- `Re(u_n ū_p)` is symmetric in `(n,p)`. -/
lemma re_mul_conj_comm (a b : ℂ) : (a * conj b).re = (b * conj a).re := by
  simp [Complex.mul_re]; ring


end MV
end Zeta23

end
open Finset Complex
open scoped BigOperators ComplexConjugate
open Zeta23
open MV
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {freq : ι → ℝ}

theorem TaoFivePrimes.hilbert_eigen_identity (hinj : Function.Injective freq) (c : ι → ℝ) (hc : ∀ r, 0 < c r)
    (u : ι → ℂ) (μ : ℝ)
    (heig : ∀ m, ∑ n ∈ Finset.univ.erase m,
        ((c m * c n / (freq m - freq n) : ℝ) : ℂ) * u n = (μ : ℂ) * Complex.I * u m)
    (m : ι) :
    μ ^ 2 * ‖u m‖ ^ 2 =
      (∑ n ∈ Finset.univ.erase m, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2)
      + 2 * ∑ n ∈ Finset.univ.erase m,
          c m ^ 3 * c n * (u m * conj (u n)).re / (freq m - freq n) ^ 2 := by
  classical
  set S : Finset ι := Finset.univ.erase m with hSdef
  have hmemS : ∀ {n : ι}, n ∈ S → n ≠ m := fun h => (Finset.mem_erase.mp h).1
  have hfr : ∀ {n p : ι}, n ≠ p → freq n - freq p ≠ 0 :=
    fun h => sub_ne_zero.mpr (fun e => h (hinj e))
  -- real coefficients a_n := c_m c_n/(λ_m − λ_n) and the real numbers R n p := Re(u_n ū_p)
  set a : ι → ℝ := fun n => c m * c n / (freq m - freq n) with hadef
  set R : ι → ι → ℝ := fun n p => (u n * conj (u p)).re with hRdef
  have hRsymm : ∀ n p, R n p = R p n := fun n p => re_mul_conj_comm _ _
  have hRdiag : ∀ n, R n n = ‖u n‖ ^ 2 := fun n => (norm_sq_eq_re_mul_conj _).symm
  /- Step A: μ²|u_m|² = Σ_n Σ_p a_n a_p R(n,p). -/
  have hA : μ ^ 2 * ‖u m‖ ^ 2 = ∑ n ∈ S, ∑ p ∈ S, a n * a p * R n p := by
    have h1 : μ ^ 2 * ‖u m‖ ^ 2 = ‖(μ : ℂ) * Complex.I * u m‖ ^ 2 := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, mul_pow,
        Real.norm_eq_abs, sq_abs]
    rw [h1, ← heig m, norm_sq_eq_re_mul_conj, map_sum, Finset.sum_mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    have : ((a n : ℝ) : ℂ) * u n * (((a p : ℝ) : ℂ) * conj (u p))
        = ((a n * a p : ℝ) : ℂ) * (u n * conj (u p)) := by push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  /- Step B: split off the diagonal. -/
  have hB : ∑ n ∈ S, ∑ p ∈ S, a n * a p * R n p
      = (∑ n ∈ S, a n * a n * R n n) + ∑ n ∈ S, ∑ p ∈ S.erase n, a n * a p * R n p := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [← Finset.add_sum_erase S _ hn]
  have hdiag : ∑ n ∈ S, a n * a n * R n n
      = ∑ n ∈ S, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2 := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have h1 := hfr (hmemS hn).symm
    rw [hRdiag]; simp only [hadef]; field_simp
  /- Step C: the off-diagonal part. G(n,p) := c_m² c_n c_p R(n,p)/((λm−λn)(λn−λp)). -/
  set G : ι → ι → ℝ := fun n p =>
    c m ^ 2 * c n * c p * R n p / ((freq m - freq n) * (freq n - freq p)) with hGdef
  have hF : ∀ n ∈ S, ∀ p ∈ S.erase n, a n * a p * R n p = G n p + G p n := by
    intro n hn p hp
    have hpn : p ≠ n := (Finset.mem_erase.mp hp).1
    have hpS : p ∈ S := (Finset.mem_erase.mp hp).2
    have h1 := hfr (hmemS hn).symm   -- freq m - freq n ≠ 0
    have h2 := hfr (hmemS hpS).symm  -- freq m - freq p ≠ 0
    have h3 := hfr hpn.symm          -- freq n - freq p ≠ 0
    have h4 := hfr hpn               -- freq p - freq n ≠ 0
    simp only [hadef, hGdef]
    rw [hRsymm p n]
    field_simp
    ring
  have hOff : ∑ n ∈ S, ∑ p ∈ S.erase n, a n * a p * R n p
      = 2 * ∑ n ∈ S, ∑ p ∈ S.erase n, G n p := by
    have hswap : ∑ n ∈ S, ∑ p ∈ S.erase n, G p n = ∑ n ∈ S, ∑ p ∈ S.erase n, G n p := by
      refine Finset.sum_comm' ?_
      intro n p
      simp only [Finset.mem_erase]
      tauto
    calc ∑ n ∈ S, ∑ p ∈ S.erase n, a n * a p * R n p
        = ∑ n ∈ S, ∑ p ∈ S.erase n, (G n p + G p n) := by
          refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun p hp => hF n hn p hp
      _ = (∑ n ∈ S, ∑ p ∈ S.erase n, G n p) + ∑ n ∈ S, ∑ p ∈ S.erase n, G p n := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun n _ => Finset.sum_add_distrib
      _ = 2 * ∑ n ∈ S, ∑ p ∈ S.erase n, G n p := by rw [hswap]; ring
  /- Step C2–C4: the inner sum, via the conjugate eigen-relation at n. -/
  have hInner : ∀ n ∈ S, ∑ p ∈ S.erase n, G n p
      = c m ^ 3 * c n * R m n / (freq m - freq n) ^ 2 := by
    intro n hn
    have hnm : n ≠ m := hmemS hn
    have h1 : freq m - freq n ≠ 0 := hfr hnm.symm
    have h1' : freq n - freq m ≠ 0 := hfr hnm
    have hcn : (c n : ℂ) ≠ 0 := by exact_mod_cast (hc n).ne'
    -- W_n := Σ_{p ∈ S.erase n} (c_p/(λn−λp)) ū_p
    set W : ℂ := ∑ p ∈ S.erase n, ((c p / (freq n - freq p) : ℝ) : ℂ) * conj (u p) with hWdef
    -- (i) Σ_p G n p = (c_m² c_n/(λm−λn)) · Re(u_n W)
    have hi : ∑ p ∈ S.erase n, G n p = c m ^ 2 * c n / (freq m - freq n) * (u n * W).re := by
      rw [hWdef, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hpn : p ≠ n := (Finset.mem_erase.mp hp).1
      have h3 : freq n - freq p ≠ 0 := hfr hpn.symm
      have : u n * (((c p / (freq n - freq p) : ℝ) : ℂ) * conj (u p))
          = ((c p / (freq n - freq p) : ℝ) : ℂ) * (u n * conj (u p)) := by ring
      rw [this, Complex.re_ofReal_mul]
      simp only [hGdef, hRdef]
      field_simp
    -- (ii) the conjugate eigen-relation at n, with the p = m term split off:
    --      c_n · (c_m/(λn−λm) ū_m + W) = −iμ ū_n
    have hii : (c n : ℂ) * ((((c m / (freq n - freq m)) : ℝ) : ℂ) * conj (u m) + W)
        = -((μ : ℂ) * Complex.I * conj (u n)) := by
      have hconj := congrArg conj (heig n)
      rw [map_sum] at hconj
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I] at hconj
      -- split p = m off the sum over univ.erase n
      have hmS : m ∈ Finset.univ.erase n := Finset.mem_erase.mpr ⟨hnm.symm, Finset.mem_univ _⟩
      have hsplit := Finset.add_sum_erase (Finset.univ.erase n)
        (fun p => ((c n * c p / (freq n - freq p) : ℝ) : ℂ) * conj (u p)) hmS
      have hSS : (Finset.univ.erase n).erase m = S.erase n := by
        rw [hSdef, Finset.erase_right_comm]
      rw [hSS] at hsplit
      rw [← hsplit] at hconj
      -- factor c n out
      have hfac : ∀ p, ((c n * c p / (freq n - freq p) : ℝ) : ℂ) * conj (u p)
          = (c n : ℂ) * (((c p / (freq n - freq p) : ℝ) : ℂ) * conj (u p)) := by
        intro p; push_cast; ring
      simp only [hfac, ← Finset.mul_sum] at hconj
      rw [hWdef]
      linear_combination hconj
    -- (iii) solve for W and take Re(u_n W): the −iμ|u_n|²/c_n piece is purely imaginary
    have hiii : (u n * W).re = -(c m / (freq n - freq m)) * R n m := by
      have hW : W = -((μ : ℂ) * Complex.I * conj (u n)) / (c n : ℂ)
          - (((c m / (freq n - freq m)) : ℝ) : ℂ) * conj (u m) := by
        field_simp
        linear_combination hii
      have hkill : (u n * (-((μ : ℂ) * Complex.I * conj (u n)) / (c n : ℂ))).re = 0 := by
        have hz : u n * conj (u n) = ((‖u n‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        have e : u n * (-((μ : ℂ) * Complex.I * conj (u n)) / (c n : ℂ))
            = -((μ : ℂ) / (c n : ℂ)) * (u n * conj (u n)) * Complex.I := by
          field_simp
        have : u n * (-((μ : ℂ) * Complex.I * conj (u n)) / (c n : ℂ))
            = ((-(μ / c n) * ‖u n‖ ^ 2 : ℝ) : ℂ) * Complex.I := by
          rw [e, hz]; push_cast; ring
        rw [this, Complex.re_ofReal_mul]; simp
      rw [hW, mul_sub, Complex.sub_re, hkill, zero_sub]
      have : u n * ((((c m / (freq n - freq m)) : ℝ) : ℂ) * conj (u m))
          = (((c m / (freq n - freq m)) : ℝ) : ℂ) * (u n * conj (u m)) := by ring
      rw [this, Complex.re_ofReal_mul]
      simp only [hRdef]; ring
    rw [hi, hiii, hRsymm n m]
    field_simp
    ring
  -- assemble
  rw [hA, hB, hdiag, hOff, Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [hInner n hn]



end

section

namespace TaoFivePrimes

open Finset Complex
open scoped ComplexConjugate

lemma sum_offdiag_comm {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (F : ι → ι → M) :
    ∑ m, ∑ n ∈ Finset.univ.erase m, F m n = ∑ n, ∑ m ∈ Finset.univ.erase n, F m n := by
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun n => Finset.univ.erase n)]
  intro n m
  simp only [Finset.mem_univ, Finset.mem_erase, true_and, and_true]
  exact ⟨Ne.symm, Ne.symm⟩

/-- Uniform inverse-square row bounds give a substantially smaller Hilbert
eigenvalue constant than the nonuniform weighted estimate. -/
theorem hilbert_eigen_bound_of_row_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (freq : ι → ℝ) (hinj : Function.Injective freq)
    (hrow : ∀ m, ∑ n ∈ Finset.univ.erase m, 1 / (freq m - freq n) ^ 2 ≤ 4)
    (u : ι → ℂ) (hu : ∑ n, ‖u n‖ ^ 2 = 1) (μ : ℝ)
    (heig : ∀ m, ∑ n ∈ Finset.univ.erase m,
      ((1 / (freq m - freq n) : ℝ) : ℂ) * u n = (μ : ℂ) * Complex.I * u m) :
    |μ| ≤ 7 / 2 := by
  let A (m n : ι) := 1 / (freq m - freq n) ^ 2
  have hA (m n : ι) : 0 ≤ A m n := by dsimp [A]; positivity
  have hsymm (m n : ι) : A m n = A n m := by dsimp [A]; congr 1; ring
  have hR : (∑ m, ∑ n ∈ Finset.univ.erase m, A m n * ‖u m‖ ^ 2) ≤ 4 := by
    calc
      _ = ∑ m, (∑ n ∈ Finset.univ.erase m, A m n) * ‖u m‖ ^ 2 := by simp_rw [Finset.sum_mul]
      _ ≤ ∑ m, 4 * ‖u m‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_right (hrow m) (sq_nonneg _)
      _ = 4 := by rw [← Finset.mul_sum, hu]; ring
  have hS : (∑ m, ∑ n ∈ Finset.univ.erase m, A m n * ‖u n‖ ^ 2) ≤ 4 := by
    rw [sum_offdiag_comm]
    simpa only [hsymm] using hR
  have hpoint (m n : ι) : 2 * (u m * conj (u n)).re ≤ ‖u m‖ ^ 2 + ‖u n‖ ^ 2 := by
    have hh := (Complex.re_le_norm (u m * conj (u n)))
    rw [norm_mul, norm_conj] at hh
    nlinarith [sq_nonneg (‖u m‖ - ‖u n‖)]
  have hT : 2 * (∑ m, ∑ n ∈ Finset.univ.erase m, A m n * (u m * conj (u n)).re) ≤ 8 := by
    calc
      _ = ∑ m, ∑ n ∈ Finset.univ.erase m, A m n * (2 * (u m * conj (u n)).re) := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ ≤ ∑ m, ∑ n ∈ Finset.univ.erase m, A m n * (‖u m‖ ^ 2 + ‖u n‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left (hpoint m n) (hA m n)
      _ ≤ 8 := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        linarith
  have hid (m : ι) := hilbert_eigen_identity hinj (fun _ => 1) (fun _ => by norm_num) u μ
    (by simpa using heig) m
  simp only [one_mul, one_pow, div_eq_mul_inv] at hid
  have hsum := congrArg (fun f : ι → ℝ => ∑ m, f m) (funext hid)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hu, mul_one] at hsum
  have he : μ ^ 2 = (∑ m, ∑ n ∈ Finset.univ.erase m, A m n * ‖u n‖ ^ 2) +
      2 * (∑ m, ∑ n ∈ Finset.univ.erase m, A m n * (u m * conj (u n)).re) := by
    simpa only [A, one_div, mul_comm] using hsum
  have hμ : μ ^ 2 ≤ 12 := by linarith
  nlinarith [sq_abs μ, abs_nonneg μ]

lemma int_inverse_square_tsum_le_four : (∑' n : ℤ, 1 / (n : ℝ) ^ 2) ≤ 4 := by
  have hs : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by decide : 1 < 2)
  have he := tsum_nat_add_neg hs
  simp only [Int.cast_neg, Int.cast_natCast, Int.cast_zero, neg_sq,
    zero_pow (by decide : 2 ≠ 0), div_zero, add_zero, ← two_mul] at he
  rw [tsum_mul_left, hasSum_zeta_two.tsum_eq] at he
  rw [← he]
  have hp := mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d2
  nlinarith
lemma integer_inverse_square_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (m : ι) :
    (∑ n ∈ Finset.univ.erase m, 1 / ((idx m : ℝ) - (idx n : ℝ)) ^ 2) ≤ 4 := by
  let φ (n : ι) := idx m - idx n
  have hi : Function.Injective φ := by
    intro a b hab
    apply hinj
    dsimp [φ] at hab
    omega
  have hsum : (∑ n ∈ Finset.univ.erase m, 1 / ((idx m : ℝ) - (idx n : ℝ)) ^ 2) =
      ∑ k ∈ (Finset.univ.erase m).image φ, 1 / (k : ℝ) ^ 2 := by
    rw [Finset.sum_image (fun a ha b hb hab => hi hab)]
    simp only [φ, Int.cast_sub]
  rw [hsum]
  apply le_trans ((Real.summable_one_div_int_pow.mpr (by decide : 1 < 2)).sum_le_tsum
    ((Finset.univ.erase m).image φ) (fun k hk => by positivity))
  exact int_inverse_square_tsum_le_four

theorem integer_hilbert_eigen_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (u : ι → ℂ)
    (hu : ∑ n, ‖u n‖ ^ 2 = 1) (μ : ℝ)
    (heig : ∀ m, ∑ n ∈ Finset.univ.erase m,
      ((1 / ((idx m : ℝ) - (idx n : ℝ)) : ℝ) : ℂ) * u n = (μ : ℂ) * Complex.I * u m) :
    |μ| ≤ 7 / 2 := by
  apply hilbert_eigen_bound_of_row_sum (fun n => (idx n : ℝ)) _ (integer_inverse_square_row idx hinj) u hu μ heig
  intro a b hab
  apply hinj
  change (idx a : ℝ) = (idx b : ℝ) at hab
  exact_mod_cast hab

end TaoFivePrimes


end

section

namespace TaoFivePrimes
open Matrix Finset
open scoped ComplexConjugate

/-- Spectral expansion of a finite Hermitian quadratic form.
Adapted from the Apache-2.0 Zeta23.MV spectral expansion (Anthropic, 2026),
using Mathlib's spectral theorem directly. -/
theorem hermitian_quadratic_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x : ι → ℂ) :
    star x ⬝ᵥ (A *ᵥ x) =
      ((∑ i, hA.eigenvalues i *
        ‖(star (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := by
  set U : Matrix ι ι ℂ := ↑hA.eigenvectorUnitary
  set c := star U *ᵥ x with hc_def
  have hsc : star x ᵥ* U = star c := by
    rw [hc_def, star_mulVec, show (star U)ᴴ = U from conjTranspose_conjTranspose U]
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec (star x) U, hsc, ← hc_def]
  simp only [Function.comp_apply, dotProduct, mulVec_diagonal, Pi.star_apply,
    Complex.star_def, RCLike.ofReal_eq_complex_ofReal]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.conj_mul', mul_left_comm]

/-- A unitary change of coordinates preserves the sum of squared moduli. -/
theorem unitary_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (x : ι → ℂ) :
    ∑ i, ‖(star (U : Matrix ι ι ℂ) *ᵥ x) i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  have he : star (star (U : Matrix ι ι ℂ) *ᵥ x) ⬝ᵥ
      (star (U : Matrix ι ι ℂ) *ᵥ x) = star x ⬝ᵥ x := by
    rw [star_mulVec, show (star (U : Matrix ι ι ℂ))ᴴ = U from
      conjTranspose_conjTranspose (U : Matrix ι ι ℂ), ← dotProduct_mulVec,
      mulVec_mulVec, ← Unitary.coe_star, Unitary.coe_mul_star_self, one_mulVec]
  have hn (v : ι → ℂ) : star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def,
      Complex.conj_mul', Complex.ofReal_sum, Complex.ofReal_pow]
  rw [hn, hn] at he
  exact_mod_cast he

theorem hermitian_quadratic_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (B : ℝ)
    (hB : ∀ i, |hA.eigenvalues i| ≤ B) (x : ι → ℂ) :
    ‖star x ⬝ᵥ (A *ᵥ x)‖ ≤ B * ∑ i, ‖x i‖ ^ 2 := by
  rw [hermitian_quadratic_expansion hA x, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ ∑ i, |hA.eigenvalues i *
        ‖(star (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ x) i‖ ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, B * ‖(star (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ x) i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_pow, abs_norm]
      exact mul_le_mul_of_nonneg_right (hB i) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, unitary_energy]

end TaoFivePrimes

end

section

namespace TaoFivePrimes
open Matrix Finset
open scoped ComplexConjugate

noncomputable def integerHilbertMatrix {ι : Type*} (idx : ι → ℤ) : Matrix ι ι ℂ :=
  fun m n => Complex.I * ((1 / ((idx m : ℝ) - (idx n : ℝ)) : ℝ) : ℂ)

lemma integerHilbertMatrix_hermitian {ι : Type*} (idx : ι → ℤ) :
    (integerHilbertMatrix idx).IsHermitian := by
  ext m n
  simp only [integerHilbertMatrix, conjTranspose_apply, map_mul, Complex.star_def,
    Complex.conj_I, Complex.conj_ofReal]
  rw [show (idx n : ℝ) - idx m = -((idx m : ℝ) - idx n) by ring]
  push_cast
  simp only [one_div, inv_neg, neg_mul, mul_neg, neg_neg]

theorem integerHilbertMatrix_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (j : ι) :
    |(integerHilbertMatrix_hermitian idx).eigenvalues j| ≤ 7 / 2 := by
  let hA := integerHilbertMatrix_hermitian idx
  let u := hA.eigenvectorBasis j
  have hu : ∑ n, ‖u n‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq]
    have hh := hA.eigenvectorBasis.orthonormal.1 j
    change ‖u‖ = 1 at hh
    rw [hh, one_pow]
  have he (m : ι) : ∑ n ∈ univ.erase m,
      ((1 / ((idx m : ℝ) - (idx n : ℝ)) : ℝ) : ℂ) * u n =
        ((-hA.eigenvalues j : ℝ) : ℂ) * Complex.I * u m := by
    have hh := congrFun (hA.mulVec_eigenvectorBasis j) m
    change (∑ n, Complex.I * ((1 / ((idx m : ℝ) - (idx n : ℝ)) : ℝ) : ℂ) * u n) =
      (hA.eigenvalues j : ℂ) * u m at hh
    have hs : (∑ n, ((1 / ((idx m : ℝ) - (idx n : ℝ)) : ℝ) : ℂ) * u n) =
        ∑ n ∈ univ.erase m, ((1 / ((idx m : ℝ) - (idx n : ℝ)) : ℝ) : ℂ) * u n := by
      rw [← sum_erase_add _ _ (mem_univ m)]
      simp
    simp_rw [mul_assoc] at hh
    rw [← mul_sum, hs] at hh
    have hmul := congrArg (fun z : ℂ => -Complex.I * z) hh
    simp only [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul] at hmul
    rw [hmul, Complex.ofReal_neg]
    ring
  have hb := integer_hilbert_eigen_bound idx hinj (fun n => u n) hu
    (-hA.eigenvalues j) he
  simpa only [abs_neg] using hb

theorem integer_hilbert_quadratic_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (x : ι → ℂ) :
    ‖star x ⬝ᵥ (integerHilbertMatrix idx *ᵥ x)‖ ≤ (7 / 2 : ℝ) * ∑ i, ‖x i‖ ^ 2 :=
  hermitian_quadratic_bound (integerHilbertMatrix_hermitian idx) (7 / 2)
    (integerHilbertMatrix_eigenvalues idx hinj) x

/-- The integer Hilbert inequality in the double-sum form needed by the sine kernel. -/
theorem integer_hilbert_sum_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (x : ι → ℂ) :
    ‖∑ m, ∑ n ∈ univ.erase m,
      star (x m) * ((1 / ((idx m : ℝ) - (idx n : ℝ)) : ℝ) : ℂ) * x n‖ ≤
        (7 / 2 : ℝ) * ∑ i, ‖x i‖ ^ 2 := by
  have he : star x ⬝ᵥ (integerHilbertMatrix idx *ᵥ x) = Complex.I *
      (∑ m, ∑ n ∈ univ.erase m,
        star (x m) * ((1 / ((idx m : ℝ) - (idx n : ℝ)) : ℝ) : ℂ) * x n) := by
    simp only [dotProduct, mulVec, integerHilbertMatrix, Pi.star_apply,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [← sum_erase_add _ _ (mem_univ m)]
    simp only [sub_self, div_zero, Complex.ofReal_zero, mul_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hb := integer_hilbert_quadratic_bound idx hinj x
  rw [he, norm_mul, Complex.norm_I, one_mul] at hb
  exact hb

end TaoFivePrimes

end

open Finset
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (x : ι → ℂ) :
    ‖∑ m, ∑ n ∈ univ.erase m,
      star (x m) * ((1 / ((idx m : ℝ) - (idx n : ℝ)) : ℝ) : ℂ) * x n‖ ≤
        (7 / 2 : ℝ) * ∑ i, ‖x i‖ ^ 2 := by
  exact TaoFivePrimes.integer_hilbert_sum_bound idx hinj x

#print axioms solution

