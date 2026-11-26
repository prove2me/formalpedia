-- Prove2me | solution 1 for QNoiseStab.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @blake-holman
-- created : 2026-11-26T04:04:15.406028+00:00
-- url     : https://prove2.me/submissions/11bf2e2e-9dd4-45d7-90c8-9a277f99c780

import Mathlib
import Definitions.Def_QNoiseStab_noiseKernel
import Definitions.Def_QNoiseStab_noiseOp
import Definitions.Def_QNoiseStab_fourierVec
import Definitions.Def_QNoiseStab_coordNoise
import Definitions.Def_QNoiseStab_singleNoiseOp

-- Solutions.Fourier
section
namespace QNoiseStab.SolutionFourier

open scoped BigOperators

variable {m n : ℕ} [NeZero m]

private theorem ket_apply (z x : ZMod m) :
    fourierKet z x = (Real.sqrt m : ℂ)⁻¹ * ZMod.stdAddChar (z * x) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rfl

private theorem star_char (x : ZMod m) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  change starRingEnd ℂ (ZMod.toCircle x : ℂ) = (ZMod.toCircle (-x) : ℂ)
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

theorem sum_ket_star (x y : ZMod m) :
    ∑ z, fourierKet z x * star (fourierKet z y) = if x = y then 1 else 0 := by
  have hs : (Real.sqrt m : ℂ) * (Real.sqrt m : ℂ) = (m : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg m)
  have hterm (z : ZMod m) :
      fourierKet z x * star (fourierKet z y) =
        (m : ℂ)⁻¹ * ZMod.stdAddChar (z * (x - y)) := by
    rw [ket_apply, ket_apply, star_mul, star_char, star_inv₀, Complex.star_def,
      Complex.conj_ofReal, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, ← hs, mul_inv]
    ring
  simp only [hterm, ← Finset.mul_sum, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar m),
    sub_eq_zero, ZMod.card]
  split_ifs <;> simp [NeZero.ne m]

theorem sum_vec_star_vec (x y : Fin n → ZMod m) :
    ∑ z, fourierVec z x * star (fourierVec z y) = if x = y then 1 else 0 := by
  classical
  change ∑ z : Fin n → ZMod m, (∏ i, fourierKet (z i) (x i)) *
    star (∏ i, fourierKet (z i) (y i)) = _
  simp only [star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i t => fourierKet t (x i) * star (fourierKet t (y i)))]
  simp only [sum_ket_star, Fintype.prod_ite_zero, Finset.prod_const_one, ← funext_iff]

theorem sum_star_vec_vec (z s : Fin n → ZMod m) :
    ∑ x, star (fourierVec z x) * fourierVec s x = if z = s then 1 else 0 := by
  classical
  have symm (u v : Fin n → ZMod m) : fourierVec u v = fourierVec v u := by
    change (∏ i, fourierKet (u i) (v i)) = ∏ i, fourierKet (v i) (u i)
    simp only [ket_apply, mul_comm (u _) (v _)]
  simpa only [symm s _, symm z _, mul_comm, eq_comm] using sum_vec_star_vec s z

end QNoiseStab.SolutionFourier
end

-- Solutions.Proposition31
section
namespace QNoiseStab

/-- **Proposition 3.1** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query
Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256
814fe20e…), p.11). For any `x, y ∈ [m]`,
`Pr[N_p(x) = y] = ⟨x| T_p |y⟩ = (1 − p) δ_{x,y} + p/m`, where `T_p = p |0̂⟩⟨0̂| + (1 − p) I`.

**Formalization Note** `[m]` is `ZMod m`; `Pr[N_p(x) = y]` is `coordNoise p x y`, cast to `ℂ`; the
matrix entry `⟨x|T_p|y⟩` is `singleNoiseOp p x y`. Both equalities are identities valid for every
real `p`. -/
theorem proposition_3_1 {m : ℕ} [NeZero m] (p : ℝ) (x y : ZMod m) :
    ((coordNoise p x y : ℝ) : ℂ) = singleNoiseOp p x y ∧
      singleNoiseOp p x y = ((1 - p) * (if x = y then 1 else 0) + p / m : ℝ) := by
  have hzero (a : ZMod m) : fourierKet (0 : ZMod m) a = ((Real.sqrt m : ℝ) : ℂ)⁻¹ := by
    simp [fourierKet]
  have hnorm : ((Real.sqrt m : ℝ) : ℂ) * (Real.sqrt m : ℝ) = (m : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg m : 0 ≤ (m : ℝ))
  have hentry : ketBra (fourierKet (0 : ZMod m)) x y = (m : ℂ)⁻¹ := by
    simp only [ketBra, Matrix.of_apply, hzero, star_inv₀, Complex.star_def, Complex.conj_ofReal,
      ← mul_inv, hnorm]
  have hformula : singleNoiseOp p x y = ((1 - p) * (if x = y then 1 else 0) + p / m : ℝ) := by
    simp only [singleNoiseOp, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hentry,
      Matrix.one_apply]
    push_cast
    split <;> simp_all [div_eq_mul_inv, add_comm]
  refine ⟨?_, hformula⟩
  rw [hformula]
  simp [coordNoise, ZMod.card, div_eq_mul_inv, add_comm]

end QNoiseStab
end

-- Solutions.Proposition32
section
namespace QNoiseStab

private theorem weighted_ket_sum {m : ℕ} [NeZero m] (p : ℝ) (x y : ZMod m) :
    ∑ z : ZMod m, (if z ≠ 0 then (1 - p : ℂ) else 1) *
      (fourierKet z x * star (fourierKet z y)) = coordNoise p x y := by
  let f (z : ZMod m) := fourierKet z x * star (fourierKet z y)
  have expand (z : ZMod m) :
      (if z ≠ 0 then (1 - p : ℂ) else 1) * f z =
        (if z = 0 then (p : ℂ) * f 0 else 0) + (1 - p) * f z := by
    by_cases hz : z = 0
    · subst z
      simp
      ring
    · simp [hz]
  change ∑ z, (if z ≠ 0 then (1 - p : ℂ) else 1) * f z = _
  simp only [expand, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [show ∑ z, f z = _ from SolutionFourier.sum_ket_star x y, (proposition_3_1 p x y).1]
  simp [singleNoiseOp, ketBra, Matrix.one_apply, f]

private theorem noiseOp_entry {n m : ℕ} [NeZero m] (p : ℝ) (A : Finset (Fin n))
    (x y : Fin n → ZMod m) : noiseOp p A y x = (noiseKernel p A x y : ℂ) := by
  classical
  let w (i : Fin n) (z : ZMod m) : ℂ :=
    if i ∈ A then (if z ≠ 0 then 1 - p else 1) else 1
  have weight (z : Fin n → ZMod m) :
      (((1 - p) ^ (A.filter fun i => z i ≠ 0).card : ℝ) : ℂ) = ∏ i, w i (z i) := by
    simp only [w, Fintype.prod_ite_mem]
    simp only [← Finset.prod_filter, Finset.prod_const,
      Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one]
  unfold noiseOp noiseKernel
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, weight, ketBra, Matrix.of_apply,
    fourierVec, WithLp.ofLp_toLp, star_prod, ← Finset.prod_mul_distrib, Complex.ofReal_prod]
  rw [← Fintype.prod_sum (fun i z => w i z * (fourierKet z (y i) * star (fourierKet z (x i))))]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ A
  · simp only [w, if_pos hi, weighted_ket_sum]
    simp [coordNoise, eq_comm]
  · simp only [w, if_neg hi, one_mul, SolutionFourier.sum_ket_star]
    by_cases hxy : x i = y i <;> simp [hxy, eq_comm]

/-- **Proposition 3.2** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query
Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256
814fe20e…), p.12). Let `x, y ∈ [m]ⁿ`. Then `Pr[N_p^A(x) = y] = ⟨y| T_p^A |x⟩`; if
`x_{[n]∖A} = y_{[n]∖A}` then
`Pr[N_p^A(x) = y] = (1 − p + p/m)^{|A| − d_A(x,y)} (p/m)^{d_A(x,y)}`, where
`d_A(x, y) = Σ_{i∈A} (1 − δ_{x_i,y_i}) = d(x, y)` is the Hamming distance between `x_A` and `y_A`;
when `x_{[n]∖A} ≠ y_{[n]∖A}`, `Pr[N_p^A(x) = y] = 0`.

**Formalization Note** `[m]` is `ZMod m`; `Pr[N_p^A(x) = y]` is `noiseKernel p A x y`; the matrix
entry `⟨y|T_p^A|x⟩` is `noiseOp p A y x`. `d_A(x, y)` is the number of `i ∈ A` with `x_i ≠ y_i`, so
the natural-number subtraction `|A| − d_A` is exact. The identities hold for every real `p`. -/
private theorem submission_proof {n m : ℕ} [NeZero m] (p : ℝ) (A : Finset (Fin n))
    (x y : Fin n → ZMod m) :
    let dA : ℕ := (A.filter fun i => x i ≠ y i).card
    ((noiseKernel p A x y : ℝ) : ℂ) = noiseOp p A y x ∧
      ((∀ i, i ∉ A → x i = y i) →
        noiseKernel p A x y = (1 - p + p / m) ^ (A.card - dA) * (p / m) ^ dA ∧
          dA = hammingDist x y) ∧
      ((∃ i, i ∉ A ∧ x i ≠ y i) → noiseKernel p A x y = 0) := by
  classical
  dsimp only
  refine ⟨(noiseOp_entry p A x y).symm, ?_, ?_⟩
  · intro hagree
    have hdist : A.filter (fun i => x i ≠ y i) = Finset.univ.filter (fun i => x i ≠ y i) := by
      ext i
      by_cases hi : i ∈ A <;> simp [hi, hagree]
    refine ⟨?_, congrArg Finset.card hdist⟩
    have hcoord (i : Fin n) : coordNoise p (x i) (y i) =
        if x i = y i then 1 - p + p / m else p / m := by
      by_cases h : x i = y i <;> simp [coordNoise, ZMod.card, h, div_eq_mul_inv, add_comm]
    have hcount := A.card_filter_add_card_filter_not (fun i => x i = y i)
    have hmatch : (A.filter fun i => x i = y i).card =
        A.card - (A.filter fun i => x i ≠ y i).card := Nat.eq_sub_of_add_eq hcount
    calc
      noiseKernel p A x y =
          ∏ i, (if i ∈ A then coordNoise p (x i) (y i) else 1) := by
        unfold noiseKernel
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : i ∈ A <;> simp [hi, hagree]
      _ = _ := by
        rw [Fintype.prod_ite_mem]
        simp only [hcoord, Finset.prod_ite, Finset.prod_const, hmatch]
  · rintro ⟨i, hi, hxy⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, hxy])

end QNoiseStab
end

section
open QNoiseStab

set_option linter.unusedVariables false in
theorem solution :
    ∀ {n m : ℕ} [NeZero m] (p : ℝ) (A : Finset (Fin n))
        (x y : Fin n → ZMod m),
      let dA : ℕ := (A.filter fun i => x i ≠ y i).card
      ((noiseKernel p A x y : ℝ) : ℂ) = noiseOp p A y x ∧
        ((∀ i, i ∉ A → x i = y i) →
          noiseKernel p A x y = (1 - p + p / m) ^ (A.card - dA) * (p / m) ^ dA ∧
            dA = hammingDist x y) ∧
        ((∃ i, i ∉ A ∧ x i ≠ y i) → noiseKernel p A x y = 0) :=
  @QNoiseStab.submission_proof

end
