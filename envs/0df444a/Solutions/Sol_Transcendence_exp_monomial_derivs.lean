-- Prove2me | solution 1 for Transcendence.exp_monomial_derivs
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T09:49:37.553908+00:00
-- url     : https://prove2.me/submissions/f36be092-12c9-4583-b8f5-56ac5e86a3f8

import Mathlib

/-!
# Derivatives of exponential monomials at algebraic points (Waldschmidt, DALAG Lemma 4.9)

Write `a_ν = φ(w_ν)` and `F_p(z) = p(z_{k₀}) · exp(Σ_ν a_ν z_ν)` for a polynomial `p ∈ ℂ[X]`. The
derivative of `F_p` along `e_j` is `F_{a_j p + [j = k₀] p'}` (`fderiv_F_single`), so by induction
on the number of directions (`deriv_poly`), the mixed partial of `g = F_{X^τ}` along `L` is
`F_{P.map φ}` for a polynomial `P ∈ K[X]` obtained from `X^τ` by the steps
`P ↦ C (w j) * P + C [j = k₀] * derivative P`. After `k` directions the coefficients satisfy:
* `natDegree P ≤ τ`;
* `house (coeff P m) ≤ A^k · C(τ,m) · k^(τ-m)` (`step_bound`, from `k^n + n k^(n-1) ≤ (k+1)^n`);
* `δ^k · coeff P m` is an algebraic integer.

At `q` with `q_{k₀} = φ v`, the value is `φ(P(v)) · exp(Σ a_ν q_ν)`. With `γ = P(v)`,
`house γ ≤ A^k Σ_m C(τ,m) k^(τ-m) B^m = A^k (B+k)^τ`, and
`δ^(k+τ) γ = Σ_m δ^(τ-m) (δ^k coeff P m) (δ v)^m` is integral.
-/

open NumberField

namespace ExpMonomialDerivs

open Polynomial
open scoped ContDiff

/-! ## Houses and integrality -/

section House

variable {K : Type*} [Field K] [NumberField K]

lemma house_zero' : house (0 : K) = 0 := by
  simpa using house_intCast (K := K) 0

lemma house_one' : house (1 : K) = 1 := by
  simpa using house_intCast (K := K) 1

lemma house_pow_le' (x : K) : ∀ n : ℕ, house (x ^ n) ≤ house x ^ n
  | 0 => by simp [house_one']
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact (house_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (house_pow_le' x n) (house_nonneg _))

omit [NumberField K] in
lemma isIntegral_intCast' (d : ℤ) : IsIntegral ℤ (d : K) := by
  simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := d))

end House

/-! ## The coefficient bound -/

/-- `k^(n+1) + (n+1) k^n ≤ (k+1)^(n+1)` for `k ≥ 0`. -/
lemma pow_succ_add_le (k : ℝ) (hk : 0 ≤ k) :
    ∀ n : ℕ, k ^ (n + 1) + ((n : ℝ) + 1) * k ^ n ≤ (k + 1) ^ (n + 1)
  | 0 => by norm_num
  | n + 1 => by
    have ih := pow_succ_add_le k hk n
    have h0 : 0 ≤ ((n : ℝ) + 1) * k ^ n := by positivity
    have h1 : (k + 1) * (k ^ (n + 1) + ((n : ℝ) + 1) * k ^ n) ≤ (k + 1) * (k + 1) ^ (n + 1) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    calc k ^ (n + 1 + 1) + (((n + 1 : ℕ) : ℝ) + 1) * k ^ (n + 1)
        = (k + 1) * (k ^ (n + 1) + ((n : ℝ) + 1) * k ^ n) - ((n : ℝ) + 1) * k ^ n := by
          push_cast; ring
      _ ≤ (k + 1) * (k + 1) ^ (n + 1) := by linarith
      _ = (k + 1) ^ (n + 1 + 1) := by ring

/-- One induction step for the coefficient bound `A^k · C(τ,m) · k^(τ-m)`. -/
lemma step_bound {A : ℝ} (hA : 1 ≤ A) (k τ m : ℕ) :
    A * (A ^ k * (τ.choose m : ℝ) * (k : ℝ) ^ (τ - m)) +
      ((m : ℝ) + 1) * (A ^ k * (τ.choose (m + 1) : ℝ) * (k : ℝ) ^ (τ - (m + 1))) ≤
    A ^ (k + 1) * (τ.choose m : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (τ - m) := by
  have hA0 : 0 ≤ A := by linarith
  rcases le_or_gt τ m with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.choose_eq_zero_of_lt (by omega : τ < m + 1)]
    apply le_of_eq
    push_cast
    ring
  · obtain ⟨n, rfl⟩ : ∃ n, τ = m + 1 + n := ⟨τ - (m + 1), by omega⟩
    have e1 : m + 1 + n - m = n + 1 := by omega
    have e2 : m + 1 + n - (m + 1) = n := by omega
    have hc : ((m + 1 + n).choose (m + 1) : ℝ) * ((m : ℝ) + 1) =
        ((m + 1 + n).choose m : ℝ) * ((n : ℝ) + 1) := by
      have := Nat.choose_succ_right_eq (m + 1 + n) m
      rw [e1] at this
      exact_mod_cast this
    rw [e1, e2]
    have hk := pow_succ_add_le (k : ℝ) (Nat.cast_nonneg k) n
    have hAk : 0 ≤ A ^ k := pow_nonneg hA0 k
    have hC : (0 : ℝ) ≤ (m + 1 + n).choose m := Nat.cast_nonneg _
    have hkn : (0 : ℝ) ≤ ((n : ℝ) + 1) * (k : ℝ) ^ n := by positivity
    have hAC : 0 ≤ A ^ k * ((m + 1 + n).choose m : ℝ) := mul_nonneg hAk hC
    calc A * (A ^ k * ((m + 1 + n).choose m : ℝ) * (k : ℝ) ^ (n + 1)) +
          ((m : ℝ) + 1) * (A ^ k * ((m + 1 + n).choose (m + 1) : ℝ) * (k : ℝ) ^ n)
        = A ^ k * ((m + 1 + n).choose m : ℝ) *
            (A * (k : ℝ) ^ (n + 1) + ((n : ℝ) + 1) * (k : ℝ) ^ n) := by
          linear_combination (A ^ k * (k : ℝ) ^ n) * hc
      _ ≤ A ^ k * ((m + 1 + n).choose m : ℝ) *
            (A * ((k : ℝ) ^ (n + 1) + ((n : ℝ) + 1) * (k : ℝ) ^ n)) := by
          refine mul_le_mul_of_nonneg_left ?_ hAC
          nlinarith
      _ ≤ A ^ k * ((m + 1 + n).choose m : ℝ) * (A * ((k : ℝ) + 1) ^ (n + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ hAC
          exact mul_le_mul_of_nonneg_left hk hA0
      _ = A ^ (k + 1) * ((m + 1 + n).choose m : ℝ) * (((k + 1 : ℕ) : ℝ)) ^ (n + 1) := by
          push_cast; ring

/-! ## The derivative of `p(z_{k₀}) · exp(Σ a_ν z_ν)` along a coordinate -/

section Analytic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `z ↦ p(z_{k₀}) · exp(Σ_ν a_ν z_ν)`. -/
noncomputable def F (k₀ : ι) (a : ι → ℂ) (p : ℂ[X]) (z : ι → ℂ) : ℂ :=
  p.eval (z k₀) * Complex.exp (∑ ν, a ν * z ν)

omit [DecidableEq ι] in
lemma hasFDerivAt_lin (a : ι → ℂ) (z : ι → ℂ) :
    HasFDerivAt (fun z : ι → ℂ => ∑ ν, a ν * z ν)
      (∑ ν, a ν • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) ν) z :=
  HasFDerivAt.fun_sum fun ν _ => (hasFDerivAt_apply (𝕜 := ℂ) ν z).const_mul (a ν)

omit [DecidableEq ι] in
lemma hasFDerivAt_F (k₀ : ι) (a : ι → ℂ) (p : ℂ[X]) (z : ι → ℂ) :
    HasFDerivAt (F k₀ a p)
      (p.eval (z k₀) • (Complex.exp (∑ ν, a ν * z ν) •
          ∑ ν, a ν • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) ν) +
        Complex.exp (∑ ν, a ν * z ν) • ((derivative p).eval (z k₀) •
          ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) k₀)) z := by
  have h1 := (p.hasDerivAt (z k₀)).comp_hasFDerivAt z
    (hasFDerivAt_apply (𝕜 := ℂ) (F' := fun _ : ι => ℂ) k₀ z)
  exact h1.mul (hasFDerivAt_lin a z).cexp

lemma fderiv_F_single (k₀ : ι) (a : ι → ℂ) (p : ℂ[X]) (z : ι → ℂ) (j : ι) :
    fderiv ℂ (F k₀ a p) z (Pi.single j 1 : ι → ℂ) =
      F k₀ a (C (a j) * p + C ((Pi.single j 1 : ι → ℂ) k₀) * derivative p) z := by
  have hs : ∑ ν, a ν * (Pi.single j 1 : ι → ℂ) ν = a j := by
    simp [Pi.single_apply]
  rw [(hasFDerivAt_F k₀ a p z).fderiv]
  simp only [add_apply, smul_apply, sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, hs, F,
    eval_add, eval_mul, eval_C]
  ring

end Analytic

/-! ## Induction on the directions -/

section Main

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField K] [Fintype ι] in
lemma map_step (φ : K →+* ℂ) (k₀ j : ι) (x : K) (P : K[X]) :
    (C x * P + C ((Pi.single j 1 : ι → K) k₀) * derivative P).map φ =
      C (φ x) * P.map φ + C ((Pi.single j 1 : ι → ℂ) k₀) * derivative (P.map φ) := by
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_C, derivative_map]
  congr 3
  rw [Pi.single_apply, Pi.single_apply]
  split_ifs <;> simp

omit [NumberField K] [DecidableEq ι] in
lemma contDiff_g (φ : K →+* ℂ) (k₀ : ι) (τ : ℕ) (w : ι → K) :
    ContDiff ℂ ω (fun z : ι → ℂ => z k₀ ^ τ * Complex.exp (∑ ν, φ (w ν) * z ν)) :=
  ((contDiff_apply ℂ ℂ k₀).pow τ).mul
    (ContDiff.cexp (ContDiff.sum fun ν _ => contDiff_const.mul (contDiff_apply ℂ ℂ ν)))

/-- The mixed partial along `L` is `F_{P.map φ}` for a polynomial `P ∈ K[X]` with the three
coefficient invariants. -/
theorem deriv_poly (φ : K →+* ℂ) (k₀ : ι) (τ : ℕ) (w : ι → K) {A : ℝ} (hA : 1 ≤ A)
    (hw : ∀ ν, house (w ν) ≤ A) (δ : ℤ) (hδw : ∀ ν, IsIntegral ℤ ((δ : K) * w ν)) :
    ∀ (k : ℕ) (L : Fin k → ι), ∃ P : K[X],
      (∀ z, iteratedFDeriv ℂ k (fun z : ι → ℂ => z k₀ ^ τ * Complex.exp (∑ ν, φ (w ν) * z ν)) z
        (fun l => Pi.single (L l) 1) = F k₀ (fun ν => φ (w ν)) (P.map φ) z) ∧
      P.natDegree ≤ τ ∧
      (∀ m, house (P.coeff m) ≤ A ^ k * (τ.choose m : ℝ) * (k : ℝ) ^ (τ - m)) ∧
      (∀ m, IsIntegral ℤ ((δ : K) ^ k * P.coeff m)) := by
  have hA0 : 0 ≤ A := by linarith
  intro k
  induction k with
  | zero =>
    intro L
    refine ⟨X ^ τ, fun z => ?_, by simp, fun m => ?_, fun m => ?_⟩
    · simp [F]
    · rw [coeff_X_pow]
      split_ifs with h
      · subst h
        simp [house_one']
      · rw [house_zero']
        positivity
    · rw [coeff_X_pow]
      split_ifs
      · simpa using (isIntegral_one (R := ℤ) (B := K))
      · simpa using (isIntegral_zero (R := ℤ) (B := K))
  | succ k ih =>
    intro L
    obtain ⟨P, hP, hdeg, hh, hi⟩ := ih (fun l => L l.succ)
    refine ⟨C (w (L 0)) * P + C ((Pi.single (L 0) 1 : ι → K) k₀) * derivative P, fun z => ?_, ?_,
      fun m => ?_, fun m => ?_⟩
    · -- the derivative formula
      rw [iteratedFDeriv_succ_apply_left, ← fderiv_continuousMultilinear_apply_const_apply
        (((contDiff_g φ k₀ τ w).differentiable_iteratedFDeriv (by simp)) z)]
      have e : (fun y => iteratedFDeriv ℂ k
          (fun z : ι → ℂ => z k₀ ^ τ * Complex.exp (∑ ν, φ (w ν) * z ν)) y
          (Fin.tail fun l => (Pi.single (L l) 1 : ι → ℂ))) =
          F k₀ (fun ν => φ (w ν)) (P.map φ) :=
        funext hP
      rw [e, fderiv_F_single, map_step]
    · -- the degree
      refine (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hdeg) ?_)
      exact (natDegree_C_mul_le _ _).trans ((natDegree_derivative_le _).trans (by omega))
    · -- the house
      rw [coeff_add, coeff_C_mul, coeff_C_mul, coeff_derivative]
      have hAk : 0 ≤ A ^ k := pow_nonneg hA0 k
      have h1 : house (w (L 0) * P.coeff m) ≤ A * (A ^ k * (τ.choose m : ℝ) * (k : ℝ) ^ (τ - m)) :=
        (house_mul_le _ _).trans (mul_le_mul (hw _) (hh m) (house_nonneg _) hA0)
      have h2 : house ((Pi.single (L 0) 1 : ι → K) k₀ * (P.coeff (m + 1) * ((m : K) + 1))) ≤
          ((m : ℝ) + 1) * (A ^ k * (τ.choose (m + 1) : ℝ) * (k : ℝ) ^ (τ - (m + 1))) := by
        have e : P.coeff (m + 1) * ((m : K) + 1) = ((m + 1 : ℕ) : K) * P.coeff (m + 1) := by
          push_cast
          ring
        rw [e, Pi.single_apply]
        split_ifs
        · rw [one_mul, house_nat_mul]
          push_cast
          exact mul_le_mul_of_nonneg_left (hh (m + 1)) (by positivity)
        · rw [zero_mul, house_zero']
          exact mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hAk (by positivity))
            (by positivity))
      exact (house_add_le _ _).trans ((add_le_add h1 h2).trans (step_bound hA k τ m))
    · -- integrality
      rw [coeff_add, coeff_C_mul, coeff_C_mul, coeff_derivative]
      have e : (δ : K) ^ (k + 1) * (w (L 0) * P.coeff m +
          (Pi.single (L 0) 1 : ι → K) k₀ * (P.coeff (m + 1) * ((m : K) + 1))) =
          ((δ : K) * w (L 0)) * ((δ : K) ^ k * P.coeff m) +
            ((δ : K) * (Pi.single (L 0) 1 : ι → K) k₀ * ((m + 1 : ℤ) : K)) *
              ((δ : K) ^ k * P.coeff (m + 1)) := by
        push_cast
        ring
      rw [e]
      refine ((hδw _).mul (hi m)).add (IsIntegral.mul ?_ (hi (m + 1)))
      refine ((isIntegral_intCast' δ).mul ?_).mul (isIntegral_intCast' _)
      rw [Pi.single_apply]
      split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero

end Main

end ExpMonomialDerivs

open ExpMonomialDerivs Polynomial in
theorem solution {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k₀ : ι) (τ : ℕ) (w : ι → K) (v : K) (q : ι → ℂ)
    (hv : 0 < τ → φ v = q k₀) {A B : ℝ} (hA : 1 ≤ A) (hw : ∀ ν, house (w ν) ≤ A)
    (hB : house v ≤ B) (δ : ℤ) (hδw : ∀ ν, IsIntegral ℤ ((δ : K) * w ν))
    (hδv : IsIntegral ℤ ((δ : K) * v)) (k : ℕ) (L : Fin k → ι) :
    ∃ γ : K, iteratedFDeriv ℂ k (fun z : ι → ℂ => z k₀ ^ τ * Complex.exp (∑ ν, φ (w ν) * z ν)) q
        (fun l => Pi.single (L l) 1) = φ γ * Complex.exp (∑ ν, φ (w ν) * q ν) ∧
      house γ ≤ A ^ k * (B + k) ^ τ ∧ IsIntegral ℤ ((δ : K) ^ (k + τ) * γ) := by
  obtain ⟨P, hP, hdeg, hh, hi⟩ := deriv_poly φ k₀ τ w hA hw δ hδw k L
  have hsum : P.eval v = ∑ m ∈ Finset.range (τ + 1), P.coeff m * v ^ m :=
    eval_eq_sum_range' (by omega) v
  refine ⟨P.eval v, ?_, ?_, ?_⟩
  · rw [hP q, F]
    congr 1
    rcases Nat.eq_zero_or_pos τ with h0 | hpos
    · subst h0
      rw [eq_C_of_natDegree_le_zero hdeg]
      simp
    · rw [← hv hpos, eval_map, eval₂_at_apply]
  · have hA0 : 0 ≤ A := by linarith
    calc house (P.eval v) ≤ ∑ m ∈ Finset.range (τ + 1), house (P.coeff m * v ^ m) := by
          rw [hsum]
          exact house_sum_le_sum_house _ _
      _ ≤ ∑ m ∈ Finset.range (τ + 1), A ^ k * (τ.choose m : ℝ) * (k : ℝ) ^ (τ - m) * B ^ m := by
          refine Finset.sum_le_sum fun m _ => ?_
          refine (house_mul_le _ _).trans (mul_le_mul (hh m) ?_ (house_nonneg _) ?_)
          · exact (house_pow_le' v m).trans (pow_le_pow_left₀ (house_nonneg v) hB m)
          · exact mul_nonneg (mul_nonneg (pow_nonneg hA0 k) (by positivity)) (by positivity)
      _ = A ^ k * (B + k) ^ τ := by
          rw [add_pow, Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by ring
  · rw [hsum, Finset.mul_sum]
    refine IsIntegral.sum _ fun m hm => ?_
    have hm' : m ≤ τ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have e : (δ : K) ^ (k + τ) * (P.coeff m * v ^ m) =
        (δ : K) ^ (τ - m) * ((δ : K) ^ k * P.coeff m) * ((δ : K) * v) ^ m := by
      rw [show k + τ = τ - m + k + m by omega]
      ring
    rw [e]
    exact (((isIntegral_intCast' δ).pow _).mul (hi m)).mul (hδv.pow m)
