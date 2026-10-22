-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P23.coherent_density_embedding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:41:35.984995+00:00
-- url     : https://prove2.me/submissions/6b81c6e5-dbec-4b85-88f0-3c034723b03f

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)


lemma g74f_vdm (l j k : ℕ) (hj : j ≤ l) (hk : k ≤ l) :
    ∑ r ∈ Finset.range (l+1), (if r + j ≤ l ∧ r + k ≤ l ∧ l ≤ j + k + r then
      (Nat.choose (l-j) r * Nat.choose j (l-k-r) : ℕ) else 0) = Nat.choose l k := by
  have h1 : Nat.choose l k = ∑ r ∈ Finset.range (l-k+1), Nat.choose (l-j) r * Nat.choose j (l-k-r) := by
    rw [← Nat.choose_symm hk]
    conv_lhs => rw [show l = (l-j) + j by omega]
    rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have : l - j + j - k = l - k := by omega
    simp only [this, Nat.succ_eq_add_one]
  rw [h1]
  calc _ = ∑ r ∈ Finset.range (l-k+1), (if r + j ≤ l ∧ r + k ≤ l ∧ l ≤ j + k + r then
      (Nat.choose (l-j) r * Nat.choose j (l-k-r) : ℕ) else 0) := by
        symm
        apply Finset.sum_subset
        · intro r hr; simp only [Finset.mem_range] at hr ⊢; omega
        · intro r _ hr
          simp only [Finset.mem_range] at hr
          rw [if_neg]; omega
    _ = _ := by
        refine Finset.sum_congr rfl fun r hr => ?_
        simp only [Finset.mem_range] at hr
        split_ifs with hg
        · rfl
        · by_cases h2 : r + j ≤ l
          · rw [Nat.choose_eq_zero_of_lt (n := j) (by omega), mul_zero]
          · rw [Nat.choose_eq_zero_of_lt (n := l-j) (by omega), zero_mul]

lemma g74f_term (l j k r : ℕ) (hg : r + j ≤ l ∧ r + k ≤ l ∧ l ≤ j + k + r) :
    (1 : ℂ) / ((Nat.factorial r : ℂ) * Nat.factorial (l - j - r) *
            Nat.factorial (l - k - r) * Nat.factorial (j + k + r - l)) =
      ((Nat.choose (l-j) r * Nat.choose j (l-k-r) : ℕ) : ℂ) / ((Nat.factorial (l-j) : ℂ) * Nat.factorial j) := by
  have e1 := Nat.choose_mul_factorial_mul_factorial (show r ≤ l - j by omega)
  have e2 := Nat.choose_mul_factorial_mul_factorial (show l - k - r ≤ j by omega)
  have h3 : j - (l - k - r) = j + k + r - l := by omega
  have h4 : l - j - r = l - j - r := rfl
  rw [h3] at e2
  have e1' : ((Nat.choose (l-j) r : ℕ) : ℂ) * (Nat.factorial r) * (Nat.factorial (l - j - r)) = Nat.factorial (l-j) := by
    exact_mod_cast e1
  have e2' : ((Nat.choose j (l-k-r) : ℕ) : ℂ) * (Nat.factorial (l-k-r)) * (Nat.factorial (j+k+r-l)) = Nat.factorial j := by
    exact_mod_cast e2
  have f1 : (Nat.factorial r : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have f2 : (Nat.factorial (l-j-r) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have f3 : (Nat.factorial (l-k-r) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have f4 : (Nat.factorial (j+k+r-l) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have f5 : (Nat.factorial (l-j) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have f6 : (Nat.factorial j : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [div_eq_div_iff (by simp [f1, f2, f3, f4]) (by simp [f5, f6])]
  push_cast
  rw [← e1', ← e2']
  ring

lemma g74f_mono (p q P Q : ℂ) (l j k r : ℕ) (hg : r + j ≤ l ∧ r + k ≤ l ∧ l ≤ j + k + r) :
    (p*P) ^ r * (p*Q) ^ (l - j - r) * (q*P) ^ (l - k - r) * (q*Q) ^ (j + k + r - l) =
      p ^ (l - j) * q ^ j * P ^ (l - k) * Q ^ k := by
  obtain ⟨s, hs⟩ : ∃ s, s = l - j - r := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = l - k - r := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = j + k + r - l := ⟨_, rfl⟩
  rw [← hs, ← ht, ← hu, show l - j = r + s by omega, show j = t + u by omega,
    show l - k = r + t by omega, show k = s + u by omega]
  simp only [mul_pow, pow_add]
  ring

lemma g74f_sqrtid (l j k : ℕ) (hj : j ≤ l) (hk : k ≤ l) :
    Real.sqrt ((Nat.factorial j : ℝ) * Nat.factorial (l - j) * Nat.factorial k * Nat.factorial (l - k)) *
      ((Nat.choose l k : ℝ) / ((Nat.factorial (l-j) : ℝ) * Nat.factorial j)) =
    Real.sqrt (Nat.choose l j : ℝ) * Real.sqrt (Nat.choose l k : ℝ) := by
  have e1 : ((Nat.choose l j : ℕ) : ℝ) * (Nat.factorial j) * (Nat.factorial (l - j)) = Nat.factorial l := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  have e2 : ((Nat.choose l k : ℕ) : ℝ) * (Nat.factorial k) * (Nat.factorial (l - k)) = Nat.factorial l := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have f5 : (0:ℝ) < (Nat.factorial (l-j) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have f6 : (0:ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have f7 : (0:ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have f8 : (0:ℝ) < (Nat.factorial (l-k) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [← Real.sqrt_mul (by positivity)]
  symm
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  have hF : Real.sqrt ((Nat.factorial j : ℝ) * Nat.factorial (l - j) * Nat.factorial k * Nat.factorial (l - k)) *
      Real.sqrt ((Nat.factorial j : ℝ) * Nat.factorial (l - j) * Nat.factorial k * Nat.factorial (l - k)) =
      (Nat.factorial j : ℝ) * Nat.factorial (l - j) * Nat.factorial k * Nat.factorial (l - k) :=
    Real.mul_self_sqrt (by positivity)
  field_simp
  rw [Real.sq_sqrt (by positivity)]
  linear_combination ((Nat.choose l k : ℝ) * (Nat.factorial j) * (Nat.factorial (l-j))) * (e1 - e2)

lemma g74f_polyPure (ell : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    polynomialIrrep ell (pureDensity psi) = pureDensity (monomialKet ell psi) := by
  funext j k
  have hj : j.val ≤ ell := by omega
  have hk : k.val ≤ ell := by omega
  simp only [polynomialIrrep, pureDensity, monomialKet, Matrix.of_apply, PiLp.toLp_apply]
  have hsum : (∑ r ∈ Finset.range (ell + 1),
      if r + j.val ≤ ell ∧ r + k.val ≤ ell ∧ ell ≤ j.val + k.val + r then
        (psi 0 * conj (psi 0)) ^ r * (psi 0 * conj (psi 1)) ^ (ell - j.val - r) *
          (psi 1 * conj (psi 0)) ^ (ell - k.val - r) * (psi 1 * conj (psi 1)) ^ (j.val + k.val + r - ell) /
          ((Nat.factorial r : ℂ) * Nat.factorial (ell - j.val - r) *
            Nat.factorial (ell - k.val - r) * Nat.factorial (j.val + k.val + r - ell))
      else 0) =
      (psi 0 ^ (ell - j.val) * psi 1 ^ j.val * conj (psi 0) ^ (ell - k.val) * conj (psi 1) ^ k.val) *
        (((Nat.choose ell k.val : ℕ) : ℂ) / ((Nat.factorial (ell - j.val) : ℂ) * Nat.factorial j.val)) := by
    rw [← g74f_vdm ell j.val k.val hj hk]
    push_cast
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs with hg
    · rw [div_eq_mul_one_div _ ((Nat.factorial r : ℂ) * _ * _ * _), g74f_term ell j.val k.val r hg,
        g74f_mono _ _ _ _ ell j.val k.val r hg]
      push_cast; ring
    · simp
  rw [hsum]
  have hs := g74f_sqrtid ell j.val k.val hj hk
  have hs' : ((Real.sqrt ((Nat.factorial j.val : ℝ) * Nat.factorial (ell - j.val) * Nat.factorial k.val * Nat.factorial (ell - k.val)) : ℝ) : ℂ) *
      (((Nat.choose ell k.val : ℕ) : ℂ) / ((Nat.factorial (ell - j.val) : ℂ) * Nat.factorial j.val)) =
      ((Real.sqrt (Nat.choose ell j.val : ℝ) : ℝ) : ℂ) * ((Real.sqrt (Nat.choose ell k.val : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← hs]; push_cast; ring
  simp only [map_mul, map_pow, Complex.conj_ofReal]
  linear_combination (psi 0 ^ (ell - j.val) * psi 1 ^ j.val * conj (psi 0) ^ (ell - k.val) * conj (psi 1) ^ k.val) * hs'
lemma g74f_physPow (ell : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) (x : QAlgorithms.Qubits ell) :
    (∏ i, psi (QAlgorithms.Papers.Independent.Support21.P18.bitIndex (x i))) =
      psi 0 ^ (ell - QAlgorithms.hammingWeight x) * psi 1 ^ QAlgorithms.hammingWeight x := by
  have h1 : ∀ i, psi (QAlgorithms.Papers.Independent.Support21.P18.bitIndex (x i)) =
      if x i = true then psi 1 else psi 0 := by
    intro i; cases x i <;> simp [QAlgorithms.Papers.Independent.Support21.P18.bitIndex]
  simp_rw [h1]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin ell))) (fun i : Fin ell => x i = true)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  unfold QAlgorithms.hammingWeight
  rw [mul_comm]
  congr 2
  omega

theorem g74f_cohEmb (ell : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    WithLp.toLp 2 ((symmetricEmbedding ell).mulVec (monomialKet ell psi)) =
      QAlgorithms.Papers.Independent.Support21.P18.physicalPower ell psi := by
  ext x
  simp only [QAlgorithms.Papers.Independent.Support21.P18.physicalPower, PiLp.toLp_apply]
  rw [g74f_physPow]
  simp only [Matrix.mulVec, dotProduct, symmetricEmbedding,
    QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding, monomialKet, PiLp.toLp_apply]
  have hle : QAlgorithms.hammingWeight x < ell + 1 := by
    have : QAlgorithms.hammingWeight x ≤ ell := by
      unfold QAlgorithms.hammingWeight
      exact (Finset.card_filter_le _ _).trans (by simp)
    omega
  rw [Finset.sum_eq_single ⟨QAlgorithms.hammingWeight x, hle⟩]
  · simp only [if_true]
    have hpos : (0:ℝ) < Real.sqrt (Nat.choose ell (QAlgorithms.hammingWeight x) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.choose_pos (by omega))
    have hne : ((Real.sqrt (Nat.choose ell (QAlgorithms.hammingWeight x) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast hpos.ne'
    field_simp
  · intro b _ hb
    rw [if_neg]; · simp
    intro h; apply hb; ext; simp [h]
  · simp


lemma g74f_conjPure {I J : Type*} [Fintype I] (A : Matrix J I ℂ) (v : EuclideanSpace ℂ I) :
    conjSuperop A (pureDensity v) = pureDensity (WithLp.toLp 2 (A.mulVec v)) := by
  funext x y
  simp only [conjSuperop, pureDensity, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
    PiLp.toLp_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [RCLike.star_def]
  ring

theorem solution (ell : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    polynomialIrrep ell (pureDensity psi) = pureDensity (monomialKet ell psi) ∧
    symmetricEmbeddingChannel ell (polynomialIrrep ell (pureDensity psi)) =
      QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower ell (pureDensity psi) := by
  refine ⟨g74f_polyPure ell psi, ?_⟩
  rw [g74f_polyPure, symmetricEmbeddingChannel, g74f_conjPure, g74f_cohEmb]
  funext x y
  simp only [pureDensity, Matrix.of_apply, QAlgorithms.Papers.Independent.Support21.P18.physicalPower,
    QAlgorithms.Papers.Independent.Support21.P18.qubitOperatorPower, Matrix.submatrix_apply,
    QAlgorithms.Papers.Independent.Information100.P63.tensorPower, PiLp.toLp_apply, map_prod]
  rw [Finset.prod_mul_distrib]

end
