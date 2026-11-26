-- Prove2me | solution 1 for QNoiseStab.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @blake-holman
-- created : 2026-11-26T04:04:16.082748+00:00
-- url     : https://prove2.me/submissions/8fdd595f-4474-4365-9f2f-a10afc9a4563

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QNoiseStab_projLowDeg
import Definitions.Def_QNoiseStab_projEvent
import Definitions.Def_QNoiseStab_noiseProb
import Definitions.Def_QNoiseStab_fourierVec
import Definitions.Def_QNoiseStab_noiseOp
import Definitions.Def_QNoiseStab_noiseKernel
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

-- Solutions.Lemma33
section
open scoped ComplexOrder

namespace QNoiseStab

/-- **Lemma 3.3** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity
and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…),
p.12). For `A ⊆ [n]`, `0 ≤ p < 1`, and every nonnegative integer `t`,
`Π_{B_t} ⪯ (1 − p)^{-t} T_p^A`.

**Formalization Note** The Loewner order `P ⪯ Q` is `(Q − P).PosSemidef`. `(1 − p)^{-t}` is
`((1 − p)^t)⁻¹` (positive since `p < 1`). `t` ranges over all of `ℕ`, including `t > n`. -/
theorem lemma_3_3 {n m : ℕ} [NeZero m] (A : Finset (Fin n)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (t : ℕ) :
    Matrix.PosSemidef (((((1 - p) ^ t)⁻¹ : ℝ) : ℂ) • (noiseOp p A : Matrix (Fin n → ZMod m)
      (Fin n → ZMod m) ℂ) - projLowDeg t) := by
  classical
  have hpos : 0 < 1 - p := sub_pos.mpr hp1
  have hunit : 1 - p ≤ 1 := by linarith
  unfold noiseOp projLowDeg
  rw [Finset.smul_sum, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Matrix.posSemidef_sum
  intro z _
  have hket : (ketBra (fourierVec z)).PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star (fun x => fourierVec z x)
  rw [smul_smul]
  by_cases hz : fourierWeight z ≤ t
  · have hcount : (A.filter fun i => z i ≠ 0).card ≤ fourierWeight z :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ A))
    have hpow := pow_le_pow_of_le_one hpos.le hunit (hcount.trans hz)
    have hscale : 1 ≤ ((1 - p) ^ t)⁻¹ * (1 - p) ^ (A.filter fun i => z i ≠ 0).card := by
      rw [← div_eq_inv_mul, le_div_iff₀ (pow_pos hpos t), one_mul]
      exact hpow
    rw [if_pos hz, ← one_smul ℂ (ketBra (fourierVec z))]
    -- Combine the scalar coefficients of this rank-one matrix.
    simp only [smul_smul, mul_one, ← sub_smul]
    apply hket.smul
    exact_mod_cast sub_nonneg.mpr hscale
  · rw [if_neg hz, sub_zero]
    apply hket.smul
    exact_mod_cast mul_nonneg (inv_nonneg.mpr (pow_nonneg hpos.le t)) (pow_nonneg hpos.le _)

end QNoiseStab
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
theorem proposition_3_2 {n m : ℕ} [NeZero m] (p : ℝ) (A : Finset (Fin n))
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

-- Solutions.Theorem34
section
namespace QNoiseStab
namespace Compression34

open scoped BigOperators NNReal Matrix MatrixOrder ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- The maximum absolute row sum bounds the spectrum in the ℓ∞ operator norm.
open scoped Matrix.Norms.Operator in
private theorem spectrum_le_rows [Nonempty ι] (M : Matrix ι ι ℂ) {r b : ℝ}
    (hr : r ∈ spectrum ℝ M) (hb : 0 ≤ b) (hrow : ∀ i, ∑ j, ‖M i j‖ ≤ b) : r ≤ b := by
  refine (Real.le_norm_self r).trans ((spectrum.norm_le_norm_of_mem hr).trans ?_)
  rw [Matrix.linfty_opNorm_def]
  change (Finset.univ.sup fun i : ι => ∑ j : ι, ‖M i j‖₊) ≤ (⟨b, hb⟩ : ℝ≥0)
  apply Finset.sup_le
  intro i _
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_sum, coe_nnnorm]
  exact hrow i

open scoped Matrix.Norms.L2Operator

-- For a positive semidefinite matrix, the ℓ² operator norm belongs to this spectrum.
private theorem psd_norm_le_rows [Nonempty ι] (M : Matrix ι ι ℂ) (hM : M.PosSemidef)
    {b : ℝ} (hb : 0 ≤ b) (hrow : ∀ i, ∑ j, ‖M i j‖ ≤ b) : ‖M‖ ≤ b :=
  spectrum_le_rows M (CStarAlgebra.norm_mem_spectrum_of_nonneg hM.nonneg) hb hrow

private theorem projector_norm_sq (P Q : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q) :
    ‖P * Q‖ ^ 2 = ‖P * Q * P‖ := by
  rw [sq, ← CStarRing.norm_self_mul_star]
  change ‖P * Q * (P * Q)ᴴ‖ = _
  rw [Matrix.conjTranspose_mul, hQ.eq, hP.eq, ← mul_assoc, mul_assoc P Q Q, hQQ]

private theorem compression_bound [Nonempty ι] (P Q R : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (hRQ : (R - Q).PosSemidef) {b : ℝ} (hb : 0 ≤ b)
    (hrow : ∀ i, ∑ j, ‖(P * R * P) i j‖ ≤ b) (v : EuclideanSpace ℂ ι) :
    ‖QAlgorithms.act (P * Q) v‖ ^ 2 ≤ b * ‖v‖ ^ 2 := by
  have hQpos := Matrix.posSemidef_self_mul_conjTranspose Q
  rw [hQ.eq, hQQ] at hQpos
  have hpos := hQpos.mul_mul_conjTranspose_same P
  rw [hP.eq] at hpos
  have hle := hRQ.mul_mul_conjTranspose_same P
  rw [hP.eq, mul_sub, sub_mul] at hle
  have hcomp := Matrix.le_iff.mpr hle
  have hRpos : 0 ≤ P * R * P := hpos.nonneg.trans hcomp
  have hnorm : ‖P * Q‖ ^ 2 ≤ b := calc
    _ = _ := projector_norm_sq P Q hP hQ hQQ
    _ ≤ ‖P * R * P‖ := CStarAlgebra.norm_le_norm_of_nonneg_of_le hpos.nonneg hcomp
    _ ≤ b := psd_norm_le_rows _ (Matrix.nonneg_iff_posSemidef.mp hRpos) hb hrow
  calc
    _ ≤ (‖P * Q‖ * ‖v‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (Matrix.l2_opNorm_mulVec (P * Q) v) 2
    _ ≤ _ := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hnorm (sq_nonneg _)

variable {n m : ℕ} [NeZero m]
private theorem lowDeg_hermitian (t : ℕ) :
    (projLowDeg (n := n) (m := m) t).IsHermitian := by
  change (∑ z ∈ _, ketBra (fourierVec z))ᴴ = _
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro z _
  change (Matrix.vecMulVec (WithLp.ofLp (fourierVec z)) (star (WithLp.ofLp (fourierVec z))))ᴴ = _
  rw [Matrix.conjTranspose_vecMulVec, star_star]
  rfl

private theorem lowDeg_idempotent (t : ℕ) :
    projLowDeg (n := n) (m := m) t * projLowDeg t = projLowDeg t := by
  classical
  have hprod (z s : Fin n → ZMod m) :
      ketBra (fourierVec z) * ketBra (fourierVec s) =
        if z = s then ketBra (fourierVec z) else 0 := by
    change Matrix.vecMulVec _ (star (WithLp.ofLp (fourierVec z))) *
      Matrix.vecMulVec (WithLp.ofLp (fourierVec s)) _ = _
    rw [Matrix.vecMulVec_mul_vecMulVec]
    change Matrix.vecMulVec _ ((∑ x, star (fourierVec z x) * fourierVec s x) • _) = _
    rw [SolutionFourier.sum_star_vec_vec]
    split_ifs with h
    · subst s
      rw [one_smul]
      rfl
    · simp
  unfold projLowDeg
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  simp_rw [Finset.mul_sum, hprod]
  simp [hz]

omit [NeZero m] in
private theorem event_hermitian (E : Finset (Fin n → ZMod m)) : (projEvent E).IsHermitian := by
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  funext x
  change star (if x ∈ E then (1 : ℂ) else 0) = _
  split_ifs <;> simp_all

private theorem kernel_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (A : Finset (Fin n))
    (x y : Fin n → ZMod m) : 0 ≤ noiseKernel p A x y := by
  apply Finset.prod_nonneg
  intro i _
  have hp : 0 ≤ 1 - p := sub_nonneg.mpr hp1.le
  simp only [coordNoise]
  split_ifs <;> positivity

private theorem kernel_symm (p : ℝ) (A : Finset (Fin n)) (x y : Fin n → ZMod m) :
    noiseKernel p A y x = noiseKernel p A x y := by
  unfold noiseKernel
  apply Finset.prod_congr rfl
  intro i _
  simp only [coordNoise, @eq_comm _ (y i) (x i)]

private theorem event_rows (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (A : Finset (Fin n))
    (E : Finset (Fin n → ZMod m)) {β c : ℝ} (hβ0 : 0 ≤ β) (hc : 0 ≤ c)
    (hβ : ∀ x ∈ E, noiseProb p A x E ≤ β)
    (x : Fin n → ZMod m) :
    ∑ y, ‖(projEvent E * ((c : ℂ) • noiseOp (m := m) p A) * projEvent E) x y‖ ≤ c * β := by
  classical
  simp only [projEvent, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ E
  · simp only [hx, if_true, one_mul]
    calc
      _ = ∑ y, if y ∈ E then c * noiseKernel p A x y else 0 := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y ∈ E
        · simp [hy, ← (proposition_3_2 p A y x).1, kernel_symm p A x y, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg (kernel_nonneg p hp0 hp1 A x y)]
        · simp [hy]
      _ = c * noiseProb p A x E := by simp [noiseProb, Finset.mul_sum]
      _ ≤ c * β := mul_le_mul_of_nonneg_left (hβ x hx) hc
  · simpa [hx] using mul_nonneg hc hβ0

end Compression34
open Compression34

-- The platform includes ht, while Lemma 3.3 applies to every natural degree bound.
set_option linter.unusedVariables false in
/-- **Theorem 3.4** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query
Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256
814fe20e…), p.12). Let `A ⊆ [n]` and `E ⊆ [m]ⁿ` be some event. If `Π_E` is the projection onto the
input states that correspond to `E`, then for `0 ≤ t ≤ n`,
`‖Π_E Π_{B_t}‖² ≤ (1 − p)^{-t} max_{x∈E} Pr[N_p^A(x) ∈ E]`.

**Formalization Note** `[m]` is `ZMod m`. The range `0 ≤ p < 1` is that of Lemma 3.3, which the
proof applies (`N_p^A` is a random variable for `p ∈ [0, 1]`, and `(1 − p)^{-t}` is undefined at
`p = 1`). The squared operator norm is stated in its equivalent pointwise form
`‖Π_E Π_{B_t} ψ‖² ≤ c ‖ψ‖²` for every vector `ψ`. The maximum is encoded by any `β ≥ 0` bounding
`Pr[N_p^A(x) ∈ E]` for every `x ∈ E` (the maximum itself is such a `β`, and `max ∅ = 0`). -/
private theorem submission_proof {n m : ℕ} [NeZero m] (A : Finset (Fin n)) (E : Finset (Fin n → ZMod m))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (t : ℕ) (ht : t ≤ n) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ∀ x ∈ E, noiseProb p A x E ≤ β) (ψ : EuclideanSpace ℂ (Fin n → ZMod m)) :
    ‖QAlgorithms.act (projEvent E * projLowDeg t) ψ‖ ^ 2 ≤
      ((1 - p) ^ t)⁻¹ * β * ‖ψ‖ ^ 2 := by
  have hc : 0 ≤ ((1 - p) ^ t)⁻¹ := inv_nonneg.mpr (pow_nonneg (sub_nonneg.mpr hp1.le) _)
  exact compression_bound (projEvent E) (projLowDeg t) _ (event_hermitian E)
    (lowDeg_hermitian t) (lowDeg_idempotent t) (lemma_3_3 A p hp0 hp1 t)
    (mul_nonneg hc hβ0) (event_rows p hp0 hp1 A E hβ0 hc hβ) ψ

end QNoiseStab
end

section
open QNoiseStab

set_option linter.unusedVariables false in
theorem solution :
    ∀ {n m : ℕ} [NeZero m] (A : Finset (Fin n)) (E : Finset (Fin n → ZMod m))
        (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (t : ℕ) (ht : t ≤ n) (β : ℝ) (hβ0 : 0 ≤ β)
        (hβ : ∀ x ∈ E, noiseProb p A x E ≤ β) (ψ : EuclideanSpace ℂ (Fin n → ZMod m)),
      ‖QAlgorithms.act (projEvent E * projLowDeg t) ψ‖ ^ 2 ≤
        ((1 - p) ^ t)⁻¹ * β * ‖ψ‖ ^ 2 :=
  @QNoiseStab.submission_proof

end
