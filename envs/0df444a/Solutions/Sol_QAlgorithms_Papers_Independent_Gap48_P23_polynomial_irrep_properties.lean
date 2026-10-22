-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P23.polynomial_irrep_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:50:24.330148+00:00
-- url     : https://prove2.me/submissions/95b8ce50-dcbe-4b69-8b0a-2cf6af997d93

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)


def g74g_mu (l : ℕ) (v : Fin 2 → ℂ) : Fin (l+1) → ℂ :=
  fun k => (Real.sqrt (l.choose k.val : ℝ) : ℂ) * v 0 ^ (l - k.val) * v 1 ^ k.val

theorem g74g_coef_real (l j r s : ℕ) (hj : j ≤ l) (hr : r ≤ l - j) (hs : s ≤ j) :
    Real.sqrt ((Nat.factorial j : ℝ) * Nat.factorial (l - j) * Nat.factorial (l - r - s) *
      Nat.factorial (l - (l - r - s))) * Real.sqrt (l.choose (l - r - s) : ℝ) =
    Real.sqrt (l.choose j : ℝ) * (l-j).choose r * j.choose s *
      ((Nat.factorial r : ℝ) * Nat.factorial (l - j - r) * Nat.factorial s *
        Nat.factorial (j - s)) := by
  have hk : l - r - s ≤ l := by omega
  set k := l - r - s
  have e1 := Nat.choose_mul_factorial_mul_factorial hr
  have e2 := Nat.choose_mul_factorial_mul_factorial hs
  have e3 := Nat.choose_mul_factorial_mul_factorial hk
  have e4 := Nat.choose_mul_factorial_mul_factorial hj
  set G : ℝ := (Nat.factorial j : ℝ) * Nat.factorial (l - j) with hG
  have hGpos : 0 < G := by positivity
  have hK : (0:ℝ) < (Nat.factorial k : ℝ) * Nat.factorial (l - k) := by positivity
  -- RHS scalar
  have hR : ((l-j).choose r : ℝ) * j.choose s * ((Nat.factorial r : ℝ) * Nat.factorial (l - j - r) *
      Nat.factorial s * Nat.factorial (j - s)) = G := by
    rw [hG, ← e1, ← e2]; push_cast; ring
  rw [show Real.sqrt (l.choose j : ℝ) * ((l-j).choose r : ℝ) * (j.choose s : ℝ) *
      ((Nat.factorial r : ℝ) * Nat.factorial (l - j - r) * Nat.factorial s * Nat.factorial (j - s)) =
      Real.sqrt (l.choose j : ℝ) * (((l-j).choose r : ℝ) * (j.choose s : ℝ) *
      ((Nat.factorial r : ℝ) * Nat.factorial (l - j - r) * Nat.factorial s * Nat.factorial (j - s))) by ring, hR]
  rw [show (Nat.factorial j : ℝ) * Nat.factorial (l - j) * Nat.factorial k * Nat.factorial (l - k) =
      G * ((Nat.factorial k : ℝ) * Nat.factorial (l - k)) by rw [hG]; ring]
  have hCk : (l.choose k : ℝ) = (Nat.factorial l : ℝ) / ((Nat.factorial k : ℝ) * Nat.factorial (l - k)) := by
    rw [← e3]; push_cast; field_simp
  have hCj : (l.choose j : ℝ) = (Nat.factorial l : ℝ) / G := by
    rw [hG, ← e4]; push_cast; field_simp
  rw [hCk, hCj, ← Real.sqrt_mul (by positivity)]
  rw [show G * (↑k.factorial * ↑(l - k).factorial) * (↑l.factorial / (↑k.factorial * ↑(l - k).factorial))
      = (↑l.factorial / G) * G^2 by field_simp]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hGpos.le]

theorem g74g_mulVec (l : ℕ) (M : Op (Fin 2)) (v : Fin 2 → ℂ) :
    (polynomialIrrep l M) *ᵥ (g74g_mu l v) = g74g_mu l (M *ᵥ v) := by
  funext j
  have hJ : j.val ≤ l := by omega
  set J := j.val with hJdef
  set f : ℕ → ℕ → ℂ := fun k r => if r + J ≤ l ∧ r + k ≤ l ∧ l ≤ J + k + r then
    (Real.sqrt ((Nat.factorial J : ℝ) * Nat.factorial (l - J) * Nat.factorial k *
      Nat.factorial (l - k)) : ℂ) *
      (M 0 0 ^ r * M 0 1 ^ (l - J - r) * M 1 0 ^ (l - k - r) * M 1 1 ^ (J + k + r - l) /
          ((Nat.factorial r : ℂ) * Nat.factorial (l - J - r) *
            Nat.factorial (l - k - r) * Nat.factorial (J + k + r - l))) *
      ((Real.sqrt (l.choose k : ℝ) : ℂ) * v 0 ^ (l - k) * v 1 ^ k) else 0 with hf
  have step1 : ((polynomialIrrep l M) *ᵥ (g74g_mu l v)) j =
      ∑ k ∈ Finset.range (l+1), ∑ r ∈ Finset.range (l+1), f k r := by
    simp only [Matrix.mulVec, dotProduct, polynomialIrrep, g74g_mu]
    rw [← Fin.sum_univ_eq_sum_range (fun k => ∑ r ∈ Finset.range (l+1), f k r)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [hf]
    split_ifs with h
    · rfl
    · simp
  rw [step1, Finset.sum_comm]
  rw [← Finset.sum_subset (s₁ := Finset.range (l - J + 1)) (s₂ := Finset.range (l+1))]
  rotate_left
  · intro r; simp only [Finset.mem_range]; omega
  · intro r _ hr
    simp only [Finset.mem_range] at hr
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [hf]; rw [if_neg (by omega)]
  -- RHS
  simp only [g74g_mu, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [add_pow, add_pow]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.range (J+1))]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  have himg : ∀ s ∈ Finset.range (J+1), ∀ t ∈ Finset.range (J+1),
      l - r - s = l - r - t → s = t := by
    intro s hs t ht h; simp only [Finset.mem_range] at hs ht; omega
  rw [← Finset.sum_subset (s₁ := (Finset.range (J+1)).image (fun s => l - r - s))
    (s₂ := Finset.range (l+1)), Finset.sum_image himg]
  rotate_left
  · intro k; simp only [Finset.mem_image, Finset.mem_range]; omega
  · intro k _ hk
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and] at hk
    simp only [hf]
    rw [if_neg]
    intro h
    exact hk (l - r - k) (by omega) (by omega)
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  have hs' : s ≤ J := by omega
  have hr' : r ≤ l - J := by omega
  simp only [hf]
  rw [if_pos (by omega)]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) (g74g_coef_real l J r s hJ hr' hs')
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at hc
  rw [show l - (l - r - s) - r = s by omega, show J + (l - r - s) + r - l = J - s by omega,
    show l - (l - r - s) = r + s by omega,
    show l - r - s = (l - J - r) + (J - s) by omega]
  rw [show l - (l - r - s) = r + s by omega, show l - r - s = (l - J - r) + (J - s) by omega] at hc
  have hden : ((Nat.factorial r : ℂ) * Nat.factorial (l - J - r) * Nat.factorial s *
      Nat.factorial (J - s)) ≠ 0 := by positivity
  rw [mul_pow, mul_pow, mul_pow, mul_pow, pow_add, pow_add]
  field_simp
  linear_combination (M 0 0 ^ r * M 0 1 ^ (l - J - r) * M 1 0 ^ s * M 1 1 ^ (J - s) *
    (v 0 ^ r * v 0 ^ s) * (v 1 ^ (l - J - r) * v 1 ^ (J - s))) * hc

theorem g74g_ext (l : ℕ) (X Y : Op (Fin (l+1)))
    (h : ∀ v : Fin 2 → ℂ, X *ᵥ g74g_mu l v = Y *ᵥ g74g_mu l v) : X = Y := by
  ext j k
  have hrow : ∀ t : ℂ, ∑ i : Fin (l+1), (X j i - Y j i) * (Real.sqrt (l.choose i.val : ℝ) : ℂ) * t ^ i.val = 0 := by
    intro t
    have := congrFun (h ![1, t]) j
    simp only [Matrix.mulVec, dotProduct, g74g_mu] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one] at this
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  set p : Polynomial ℂ := ∑ i : Fin (l+1),
    Polynomial.C ((X j i - Y j i) * (Real.sqrt (l.choose i.val : ℝ) : ℂ)) * Polynomial.X ^ i.val with hp
  have hp0 : p = 0 := by
    apply Polynomial.funext
    intro t
    rw [hp, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_zero]
    exact hrow t
  have hcoef := congrArg (fun q => Polynomial.coeff q k.val) hp0
  simp only [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hcoef
  rw [Finset.sum_eq_single k] at hcoef
  · rw [if_pos rfl] at hcoef
    have hne : (Real.sqrt (l.choose k.val : ℝ) : ℂ) ≠ 0 := by
      have : 0 < Real.sqrt (l.choose k.val : ℝ) := Real.sqrt_pos.mpr (by
        exact_mod_cast Nat.choose_pos (by omega))
      exact_mod_cast this.ne'
    have := (mul_eq_zero.mp hcoef).resolve_right hne
    exact sub_eq_zero.mp this
  · intro b _ hb
    rw [if_neg (fun h => hb (Fin.ext h.symm))]
  · simp

theorem g74g_mu_smul (l : ℕ) (z : ℂ) (v : Fin 2 → ℂ) :
    g74g_mu l (z • v) = z ^ l • g74g_mu l v := by
  funext k
  have hk : k.val ≤ l := by omega
  simp only [g74g_mu, Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [show z ^ l = z ^ (l - k.val) * z ^ k.val by rw [← pow_add]; congr 1; omega]
  ring

theorem g74g_mul (l : ℕ) (A B : Op (Fin 2)) :
    polynomialIrrep l (A * B) = polynomialIrrep l A * polynomialIrrep l B := by
  apply g74g_ext; intro v
  rw [g74g_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, g74g_mulVec, g74g_mulVec]

theorem g74g_smul (l : ℕ) (z : ℂ) (M : Op (Fin 2)) :
    polynomialIrrep l (z • M) = z ^ l • polynomialIrrep l M := by
  apply g74g_ext; intro v
  rw [g74g_mulVec, Matrix.smul_mulVec, g74g_mu_smul, Matrix.smul_mulVec, g74g_mulVec]

theorem g74g_one (l : ℕ) : polynomialIrrep l 1 = 1 := by
  apply g74g_ext; intro v
  rw [g74g_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]

theorem g74g_diag (l : ℕ) (a d : ℂ) : polynomialIrrep l (Matrix.diagonal ![a,d]) =
      Matrix.diagonal (fun k : Fin (l+1) => a^(l-k.val)*d^k.val) := by
  apply g74g_ext; intro v
  rw [g74g_mulVec]
  funext k
  simp only [g74g_mu, Matrix.mulVec_diagonal, Matrix.cons_val_zero, Matrix.cons_val_one, mul_pow]
  ring

theorem g74g_single (l : ℕ) : polynomialIrrep l (Matrix.single 0 0 1) = Matrix.single 0 0 1 := by
  apply g74g_ext; intro v
  rw [g74g_mulVec]
  funext k
  simp only [g74g_mu, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.single_apply]
  by_cases hk : k = 0
  · subst hk
    simp
  · have hk' : k.val ≠ 0 := fun h => hk (Fin.ext h)
    simp [Ne.symm hk, zero_pow hk']

theorem g74g_transpose (l : ℕ) (M : Op (Fin 2)) :
    polynomialIrrep l M.transpose = (polynomialIrrep l M).transpose := by
  ext j k
  simp only [polynomialIrrep, Matrix.transpose_apply]
  congr 1
  · congr 2; ring
  · refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h : r + j.val ≤ l ∧ r + k.val ≤ l ∧ l ≤ j.val + k.val + r
    · rw [if_pos h, if_pos ⟨h.2.1, h.1, by omega⟩, show k.val + j.val + r - l = j.val + k.val + r - l by omega]
      ring
    · rw [if_neg h, if_neg (by omega)]

theorem g74g_conj (l : ℕ) (M : Op (Fin 2)) :
    polynomialIrrep l (fun i j => conj (M i j)) = (fun i j => conj (polynomialIrrep l M i j)) := by
  funext j k
  simp only [polynomialIrrep, map_mul, map_sum, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs
  · simp [map_div₀, map_mul, map_pow, map_natCast]
  · simp

theorem g74g_conjTranspose (l : ℕ) (M : Op (Fin 2)) :
    polynomialIrrep l Mᴴ = (polynomialIrrep l M)ᴴ := by
  set C : Op (Fin 2) := fun i j => conj (M i j) with hC
  have h1 : Mᴴ = C.transpose := Matrix.ext fun i j => rfl
  rw [h1, g74g_transpose, hC, g74g_conj]
  exact Matrix.ext fun i j => rfl

/-- PDF pp.59-60, Appendix C.2: all concrete polynomial representation
properties, including the SVD transport with its nonnegative singular values. -/
theorem solution (ell : ℕ) :
    (∀ A B : Op (Fin 2), polynomialIrrep ell (A*B) = polynomialIrrep ell A * polynomialIrrep ell B) ∧
    (∀ (z : ℂ) (M : Op (Fin 2)), polynomialIrrep ell (z • M) = z^ell • polynomialIrrep ell M) ∧
    (∀ a d : ℂ, polynomialIrrep ell (Matrix.diagonal ![a,d]) =
      Matrix.diagonal (fun k : Fin (ell+1) => a^(ell-k.val)*d^k.val)) ∧
    polynomialIrrep ell 1 = 1 ∧
    polynomialIrrep ell (Matrix.single 0 0 1) = Matrix.single 0 0 1 ∧
    (∀ M : Op (Fin 2), polynomialIrrep ell M.transpose = (polynomialIrrep ell M).transpose ∧
      polynomialIrrep ell (fun i j => conj (M i j)) = (fun i j => conj (polynomialIrrep ell M i j)) ∧
      polynomialIrrep ell Mᴴ = (polynomialIrrep ell M)ᴴ) ∧
    (∀ U : Matrix.unitaryGroup (Fin 2) ℂ,
      (polynomialIrrep ell U.val)ᴴ * polynomialIrrep ell U.val = 1 ∧
      polynomialIrrep ell U.val * (polynomialIrrep ell U.val)ᴴ = 1) ∧
    (∀ (U V : Matrix.unitaryGroup (Fin 2) ℂ) (a d : ℝ), 0 ≤ a → 0 ≤ d →
      polynomialIrrep ell (U.val * Matrix.diagonal ![(a:ℂ),(d:ℂ)] * V.valᴴ) =
        polynomialIrrep ell U.val *
          Matrix.diagonal (fun k : Fin (ell+1) => ((a^(ell-k.val)*d^k.val : ℝ) : ℂ)) *
          (polynomialIrrep ell V.val)ᴴ) := by
  refine ⟨g74g_mul ell, g74g_smul ell, g74g_diag ell, g74g_one ell, g74g_single ell,
    fun M => ⟨g74g_transpose ell M, g74g_conj ell M, g74g_conjTranspose ell M⟩, ?_, ?_⟩
  · intro U
    have h1 : U.val.conjTranspose * U.val = 1 := by
      have := U.2; rw [Matrix.mem_unitaryGroup_iff'] at this; exact this
    have h2 : U.val * U.val.conjTranspose = 1 := by
      have := U.2; rw [Matrix.mem_unitaryGroup_iff] at this; exact this
    constructor
    · rw [← g74g_conjTranspose, ← g74g_mul, h1, g74g_one]
    · rw [← g74g_conjTranspose, ← g74g_mul, h2, g74g_one]
  · intro U V a d _ _
    rw [g74g_mul, g74g_mul, g74g_diag, g74g_conjTranspose]
    congr 3
    funext k
    push_cast
    ring


end
