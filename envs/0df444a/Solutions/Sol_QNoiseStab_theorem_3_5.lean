-- Prove2me | solution 1 for QNoiseStab.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @blake-holman
-- created : 2026-11-26T04:04:16.745691+00:00
-- url     : https://prove2.me/submissions/48c40549-f1c0-4b1d-9e4a-fafce18490f4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QNoiseStab_successProb
import Definitions.Def_QNoiseStab_noiseProb
import Definitions.Def_QNoiseStab_eventSet
import Definitions.Def_QNoiseStab_phaseQuery
import Definitions.Def_QNoiseStab_fourierWeight
import Definitions.Def_QNoiseStab_fourierVec
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QNoiseStab_projEvent
import Definitions.Def_QNoiseStab_projLowDeg
import Definitions.Def_QNoiseStab_noiseOp
import Definitions.Def_QNoiseStab_noiseKernel
import Definitions.Def_QNoiseStab_coordNoise
import Definitions.Def_QNoiseStab_singleNoiseOp

-- Solutions.Corollary29
section
namespace QNoiseStab

section

variable {n d : ℕ}

/-- Finite sums of functions that each depend on at most `t` coordinates. -/
inductive JuntaSum (t : ℕ) : ((Fin n → ZMod d) → ℂ) → Prop where
  | junta (s : Finset (Fin n)) (hs : s.card ≤ t) (f : (Fin n → ZMod d) → ℂ)
      (hf : ∀ x y, (∀ i ∈ s, x i = y i) → f x = f y) : JuntaSum t f
  | sum {ι : Type} [Fintype ι] (f : ι → (Fin n → ZMod d) → ℂ)
      (hf : ∀ j, JuntaSum t (f j)) : JuntaSum t (fun x => ∑ j, f j x)

theorem JuntaSum.mul_unary {t : ℕ} {f : (Fin n → ZMod d) → ℂ} (hf : JuntaSum t f)
    (i : Fin n) (g : ZMod d → ℂ) : JuntaSum (t + 1) (fun x => g (x i) * f x) := by
  induction hf with
  | junta s hs f hf =>
    apply JuntaSum.junta (insert i s) ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ hs))
    intro x y h
    rw [h i (Finset.mem_insert_self ..), hf x y (fun j hj => h j (Finset.mem_insert_of_mem hj))]
  | sum f hf ih =>
    simp only [Finset.mul_sum]
    exact JuntaSum.sum _ ih

theorem JuntaSum.const (t : ℕ) (c : ℂ) :
    JuntaSum (n := n) (d := d) t (fun _ => c) :=
  .junta ∅ (by simp) _ (fun _ _ _ => rfl)

theorem JuntaSum.const_mul {t : ℕ} {f : (Fin n → ZMod d) → ℂ} (hf : JuntaSum t f) (c : ℂ) :
    JuntaSum t (fun x => c * f x) := by
  induction hf with
  | junta s hs f hf => exact .junta s hs _ (fun x y h => congrArg (c * ·) (hf x y h))
  | sum f hf ih =>
    simp only [Finset.mul_sum]
    exact .sum _ ih

theorem JuntaSum.matrix_mulVec {I J : Type} [Fintype J] {t : ℕ} (M : Matrix I J ℂ)
    (v : (Fin n → ZMod d) → J → ℂ) (h : ∀ j, JuntaSum t (fun x => v x j)) (i : I) :
    JuntaSum t (fun x => M.mulVec (v x) i) :=
  .sum _ (fun j => (h j).const_mul (M i j))

variable [NeZero d]

private lemma phase_act {W : Type} [Fintype W] [DecidableEq W] (ω : ℂ)
    (x : Fin n → ZMod d) (ψ : EuclideanSpace ℂ ((Fin n × ZMod d) × W))
    (p : (Fin n × ZMod d) × W) :
    QAlgorithms.act (Matrix.kronecker (phaseQuery ω x) (1 : Matrix W W ℂ)) ψ p =
      ω ^ (p.1.2 * x p.1.1).val * ψ p := by
  unfold phaseQuery Matrix.kronecker
  rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
  exact (Matrix.mulVec_diagonal _ _ _).trans (by simp)

private lemma state_juntaSum {W : Type} [Fintype W] [DecidableEq W] {T : ℕ}
    (ω : ℂ) (alg : QAlgorithms.QueryAlg (Fin n) (ZMod d) W T) (t : Fin (T + 1)) :
    ∀ q, JuntaSum t.val (fun x => alg.stateAt (phaseQuery ω x) t q) := by
  induction t using Fin.induction with
  | zero =>
    intro q
    exact JuntaSum.junta ∅ (by simp) _ (fun _ _ _ => rfl)
  | succ i ih =>
    intro q
    simp only [QAlgorithms.QueryAlg.stateAt, Fin.induction_succ]
    change JuntaSum (i.val + 1) (fun x => ∑ p, (alg.U i.succ : Matrix _ _ ℂ) q p *
      QAlgorithms.act (Matrix.kronecker (phaseQuery ω x) (1 : Matrix W W ℂ))
        (alg.stateAt (phaseQuery ω x) i.castSucc) p)
    simp only [phase_act, ← mul_assoc]
    exact JuntaSum.sum _ (fun p => JuntaSum.mul_unary (ih p) p.1.1
      (fun a => (alg.U i.succ : Matrix _ _ ℂ) q p * ω ^ (p.1.2 * a).val))

private lemma sum_star_ket {w : ZMod d} (hw : w ≠ 0) :
    ∑ a : ZMod d, star (fourierKet w a) = 0 := by
  have hchar (a : ZMod d) :
      Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) / (d : ℂ)) = ZMod.stdAddChar a := by
    simpa using (ZMod.stdAddChar_coe (N := d) (a.val : ℤ)).symm
  have hzero : ∑ a : ZMod d, ZMod.stdAddChar (w * a) = 0 :=
    AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar d hw)
  rw [← star_sum]
  change star (∑ a : ZMod d, ((Real.sqrt d)⁻¹ : ℂ) * _) = 0
  simp only [hchar, ← Finset.mul_sum, hzero, mul_zero, star_zero]

private lemma junta_fourier_zero (s : Finset (Fin n)) (f : (Fin n → ZMod d) → ℂ)
    (hf : ∀ x y, (∀ j ∈ s, x j = y j) → f x = f y)
    (z : Fin n → ZMod d) (hz : s.card < fourierWeight z) :
    ∑ x, star (fourierVec z x) * f x = 0 := by
  classical
  obtain ⟨i, hzi, his⟩ := Finset.exists_mem_notMem_of_card_lt_card hz
  have hne : z i ≠ 0 := (Finset.mem_filter.mp hzi).2
  let e := Equiv.funSplitAt i (ZMod d)
  rw [← e.symm.sum_comp (fun x => star (fourierVec z x) * f x), Fintype.sum_prod_type_right]
  apply Finset.sum_eq_zero
  intro y _
  let x (a : ZMod d) := e.symm (a, y)
  have hxi (a) : x a i = a := by simp [x, e, Equiv.funSplitAt_symm_apply]
  have hoff (a) (j : Fin n) (hj : j ≠ i) : x a j = x 0 j := by
    simp [x, e, Equiv.funSplitAt_symm_apply, hj]
  have hproduct (a) : fourierVec z (x a) =
      fourierKet (z i) a * ∏ j ∈ Finset.univ.erase i, fourierKet (z j) (x 0 j) := by
    change ∏ j, fourierKet (z j) (x a j) = _
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), hxi]
    congr 1
    exact Finset.prod_congr rfl (fun j hj => by rw [hoff a j (Finset.ne_of_mem_erase hj)])
  have hf' (a) : f (x a) = f (x 0) := hf _ _ (fun j hj => hoff a j (fun h => his (h ▸ hj)))
  change ∑ a, star (fourierVec z (x a)) * f (x a) = 0
  simp only [hproduct, star_mul', hf', mul_assoc, ← Finset.sum_mul, sum_star_ket hne, zero_mul]

theorem JuntaSum.fourier_zero {t : ℕ} {f : (Fin n → ZMod d) → ℂ} (hf : JuntaSum t f)
    (z : Fin n → ZMod d) (hz : t < fourierWeight z) :
    ∑ x, star (fourierVec z x) * f x = 0 := by
  induction hf with
  | junta s hs f hf => exact junta_fourier_zero s f hf z (lt_of_le_of_lt hs hz)
  | sum f hf ih =>
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero (fun j _ => ih j)

end

-- The published statement assumes a root of unity. The degree bound uses only locality.
set_option linter.unusedVariables false in
/-- **Corollary 2.9** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query
Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256
814fe20e…), p.10, in the setting of p.9: "We focus on the domain X = Zm and the input
distribution being the uniform distribution on Xn"). The state of any quantum query algorithm
that makes at most `t` queries to its input is a linear combination of states whose input register
in the Fourier basis `|ẑ⟩` has the property that `z` contains at most `t` non-0 entries.

Stated for every `T`-query algorithm `alg` with phase queries `phaseQuery ω x` (`ω ^ d = 1`) on
inputs `x ∈ Z_dⁿ`, every number of queries `t ≤ T` (the intermediate state `alg.stateAt _ t`),
every computational basis state `q` of the algorithm registers `QPW`, and every frequency `z` with
more than `t` nonzero entries: `Σ_x conj(⟨x|ẑ⟩) · ⟨q|ψ_t^x⟩ = 0`.

**Formalization Note** For the uniform input the joint state after `t` queries is
`Σ_x d^{-n/2} |ψ_t^x⟩|x⟩`; its input-register component at the basis state `q` is
`φ_q = Σ_x d^{-n/2} ψ_t^x(q) |x⟩`, and `⟨ẑ|φ_q⟩` is `d^{-n/2}` times the displayed sum. "A linear
combination of `|q⟩ ⊗ |ẑ⟩` with at most `t` nonzero `z_i`" is exactly the vanishing of this sum for
every `q` and every `z` of weight `> t`. The Fourier basis uses the primitive root `exp(2πi/d)`;
the oracle root `ω` is any `d`-th root of unity. -/
theorem corollary_2_9 {W : Type} [Fintype W] [DecidableEq W] {n d T : ℕ} [NeZero d] (ω : ℂ)
    (hω : ω ^ d = 1) (alg : QAlgorithms.QueryAlg (Fin n) (ZMod d) W T) (t : Fin (T + 1))
    (q : (Fin n × ZMod d) × W) (z : Fin n → ZMod d) (hz : t.val < fourierWeight z) :
    ∑ x : Fin n → ZMod d, star (fourierVec z x) * alg.stateAt (phaseQuery ω x) t q = 0 := by
  exact JuntaSum.fourier_zero (state_juntaSum ω alg t q) z hz

end QNoiseStab
end

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
theorem theorem_3_4 {n m : ℕ} [NeZero m] (A : Finset (Fin n)) (E : Finset (Fin n → ZMod m))
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

-- Solutions.QuerySuccess
section
/-! # Fourier projection, normalisation and summation of the output probabilities -/

noncomputable section

namespace QNoiseStab.SolutionSuccess

open Finset QAlgorithms

variable {n d T : ℕ} [NeZero d]

theorem projLow_fixed (t : ℕ) (v : EuclideanSpace ℂ (Fin n → ZMod d))
    (hcoeff : ∀ z, t < fourierWeight z → ∑ y, star (fourierVec z y) * v y = 0)
    (hcomplete : ∀ x y : Fin n → ZMod d,
      ∑ z, fourierVec z x * star (fourierVec z y) = if x = y then 1 else 0) :
    act (projLowDeg t) v = v := by
  classical
  ext x
  let coeff (z : Fin n → ZMod d) := ∑ y, star (fourierVec z y) * v y
  have expand (s : Finset (Fin n → ZMod d)) :
      (act (∑ z ∈ s, ketBra (fourierVec z)) v) x = ∑ z ∈ s, fourierVec z x * coeff z := by
    change ∑ y, (∑ z ∈ s, ketBra (fourierVec z)) x y * v y = _
    simp only [Matrix.sum_apply, ketBra, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [coeff, Finset.mul_sum, mul_assoc]
  rw [projLowDeg, expand, Finset.sum_filter]
  calc ∑ z, (if fourierWeight z ≤ t then fourierVec z x * coeff z else 0) =
          ∑ z, fourierVec z x * coeff z := by
        apply sum_congr rfl
        intro z _
        split_ifs with hz
        · rfl
        · rw [show coeff z = 0 from hcoeff z (lt_of_not_ge hz), mul_zero]
    _ = ∑ y, (∑ z, fourierVec z x * star (fourierVec z y)) * v y := by
      simp only [coeff, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact sum_comm
    _ = v x := by simp_rw [hcomplete]; simp [ite_mul]

theorem event_projection_norm (E : Finset (Fin n → ZMod d)) (v : EuclideanSpace ℂ (Fin n → ZMod d)) :
    ‖act (projEvent E) v‖ ^ 2 = ∑ x ∈ E, ‖v x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc ∑ x, ‖act (projEvent E) v x‖ ^ 2 = ∑ x, if x ∈ E then ‖v x‖ ^ 2 else 0 := by
        apply sum_congr rfl
        intro x _
        by_cases hx : x ∈ E <;> simp [act, projEvent, Matrix.mulVec_diagonal, hx]
    _ = _ := by rw [← sum_filter]; simp

theorem act_product {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (A * B) v = act A (act B v) := by
  unfold act
  simp [Matrix.mulVec_mulVec]

theorem phase_norm {W : Type} [Fintype W] [DecidableEq W] (ω : ℂ) (hω : ω ^ d = 1)
    (x : Fin n → ZMod d) (v : EuclideanSpace ℂ ((Fin n × ZMod d) × W)) :
    ‖act (Matrix.kronecker (phaseQuery ω x) (1 : Matrix W W ℂ)) v‖ = ‖v‖ := by
  have hroot : ‖ω‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg ω) (NeZero.ne d)).mp
      (by simpa only [norm_pow, norm_one] using congrArg norm hω)
  let f (q : Fin n × ZMod d) := ω ^ (q.2 * x q.1).val
  have hmat : Matrix.kronecker (phaseQuery ω x) (1 : Matrix W W ℂ) =
      Matrix.diagonal (fun q : (Fin n × ZMod d) × W => f q.1) := by
    change Matrix.kronecker (Matrix.diagonal f) (1 : Matrix W W ℂ) = _
    unfold Matrix.kronecker
    rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
    simp
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hmat, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [act, Matrix.mulVec_diagonal, f, norm_pow, hroot]

theorem state_norm {W : Type} [Fintype W] [DecidableEq W] (ω : ℂ) (hω : ω ^ d = 1)
    (alg : QueryAlg (Fin n) (ZMod d) W T) (x : Fin n → ZMod d) (t : Fin (T+1)) :
    ‖alg.stateAt (phaseQuery ω x) t‖ = 1 := by
  induction t using Fin.induction with
  | zero =>
    change ‖act _ alg.start‖ = 1
    exact (act_norm_of_mem_unitaryGroup (alg.U 0).property _).trans alg.start_unit
  | succ t ih =>
    change ‖act (alg.U t.succ : Matrix _ _ ℂ) (act (Matrix.kronecker (phaseQuery ω x) 1)
      (alg.stateAt (phaseQuery ω x) t.castSucc))‖ = 1
    rw [act_norm_of_mem_unitaryGroup (alg.U t.succ).property, phase_norm ω hω, ih]

theorem mass_sum {X K : Type} [Fintype X] [Fintype K] [DecidableEq X]
    (w : X → K → ℝ) (hw : ∀ x k, 0 ≤ w x k) (hone : ∀ x, ∑ k, w x k = 1)
    (free : Finset X) (R : X → K → Prop) [DecidableRel R] {c : ℝ}
    (hbound : ∀ k, ∑ x ∈ univ.filter (fun x => x ∉ free ∧ R x k), w x k ≤ c * ∑ x, w x k) :
    ∑ x, ∑ k, (if R x k then w x k else 0) ≤ c * Fintype.card X + free.card := by
  classical
  calc ∑ x, ∑ k, (if R x k then w x k else 0)
      ≤ ∑ x, ((∑ k, if x ∉ free ∧ R x k then w x k else 0) + if x ∈ free then 1 else 0) := by
        apply sum_le_sum
        intro x _
        by_cases hx : x ∈ free
        · simp only [hx, not_true_eq_false, false_and, if_false, sum_const_zero, if_true, zero_add]
          rw [← hone x]
          exact sum_le_sum fun k _ => by split_ifs <;> first | rfl | exact hw x k
        · simp [hx]
    _ = (∑ k, ∑ x ∈ univ.filter (fun x => x ∉ free ∧ R x k), w x k) + free.card := by
        rw [sum_add_distrib, sum_comm]
        simp [sum_filter]
    _ ≤ ∑ k, (c * ∑ x, w x k) + free.card := by
        exact add_le_add (sum_le_sum fun k _ => hbound k) le_rfl
    _ = c * Fintype.card X + free.card := by
        rw [← mul_sum, sum_comm]
        simp [hone]

end QNoiseStab.SolutionSuccess
end
end

-- Solutions.Theorem35
section
/-! # Quantum noise stability for a finite input alphabet -/

noncomputable section

namespace QNoiseStab

open Finset QAlgorithms
open SolutionSuccess

private def encodeInputs {X G : Type} {n : ℕ} (enc : X ≃ G) : (Fin n → X) ≃ (Fin n → G) :=
  Equiv.piCongrRight fun _ => enc

private theorem noiseProb_encode {X G : Type} [Fintype X] [Fintype G] [DecidableEq X]
    [DecidableEq G] {n : ℕ} (enc : X ≃ G) (p : ℝ) (A : Finset (Fin n))
    (x : Fin n → X) (E : Finset (Fin n → X)) :
    noiseProb p A (encodeInputs enc x) (E.map (encodeInputs enc).toEmbedding) = noiseProb p A x E := by
  classical
  simp [noiseProb, noiseKernel, coordNoise, encodeInputs, Fintype.card_congr enc]

private theorem submission_proof {X Ŷ W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
    {n d T : ℕ} [NeZero d] (enc : X ≃ ZMod d) (ω : ℂ) (hω : ω ^ d = 1)
    (R : Set ((Fin n → X) × Ŷ)) (A : Finset (Fin n)) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (Efree : Finset (Fin n → X)) (hT : T ≤ n) (alg : QAlgorithms.QueryAlg (Fin n) (ZMod d) W T)
    (out : (Fin n × ZMod d) × W → Ŷ) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ∀ y : Ŷ, ∀ x ∈ eventSet Efree R y, noiseProb p A x (eventSet Efree R y) ≤ β) :
    successProb enc ω alg out R ≤
        2 * ((1 - p) ^ T)⁻¹ * β + 2 * (Efree.card : ℝ) / (Fintype.card X : ℝ) ^ n ∧
      (Efree = ∅ → successProb enc ω alg out R ≤ ((1 - p) ^ T)⁻¹ * β) := by
  classical
  let e := encodeInputs (n := n) enc
  have he (x : Fin n → X) : e x = fun i => enc (x i) := rfl
  let amp (q : (Fin n × ZMod d) × W) : EuclideanSpace ℂ (Fin n → ZMod d) :=
    WithLp.toLp 2 fun x => alg.finalState (phaseQuery ω x) q
  let c := ((1-p)^T)⁻¹ * β
  have hnorm (x : Fin n → X) : ∑ q, ‖amp q (e x)‖ ^ 2 = 1 := by
    change ∑ q, ‖alg.finalState (phaseQuery ω (e x)) q‖ ^ 2 = 1
    rw [← EuclideanSpace.norm_sq_eq, QueryAlg.finalState, state_norm ω hω alg, one_pow]
  have hbranch (q : (Fin n × ZMod d) × W) :
      ∑ x ∈ eventSet Efree R (out q), ‖amp q (e x)‖ ^ 2 ≤ c * ∑ x, ‖amp q (e x)‖ ^ 2 := by
    let E := (eventSet Efree R (out q)).map e.toEmbedding
    have hrow (z : Fin n → ZMod d) (hz : z ∈ E) : noiseProb p A z E ≤ β := by
      obtain ⟨x, hx, rfl⟩ := mem_map.mp hz
      exact (noiseProb_encode enc p A x _).le.trans (hβ (out q) x hx)
    have hproj : act (projLowDeg T) (amp q) = amp q :=
      projLow_fixed T (amp q) (fun z hz => corollary_2_9 ω hω alg (Fin.last T) q z hz)
        SolutionFourier.sum_vec_star_vec
    have h := theorem_3_4 A E p hp.1.le hp.2 T hT β hβ0 hrow (amp q)
    rw [act_product, hproj, event_projection_norm, EuclideanSpace.norm_sq_eq] at h
    rw [e.sum_comp (fun z => ‖amp q z‖ ^ 2)]
    simpa only [E, sum_map, Function.Embedding.coeFn_mk, Equiv.coe_toEmbedding] using h
  have hsum := mass_sum (fun x q => ‖amp q (e x)‖ ^ 2) (fun _ _ => sq_nonneg _) hnorm
    Efree (fun x q => (x, out q) ∈ R) hbranch
  have : Nonempty X := ⟨enc.symm 0⟩
  have hc : 0 ≤ c := mul_nonneg (inv_nonneg.mpr (pow_nonneg (sub_nonneg.mpr hp.2.le) _)) hβ0
  have hcount : 0 < (Fintype.card X : ℝ) ^ n := by positivity
  have hsuccess : successProb enc ω alg out R ≤ c + Efree.card / (Fintype.card X : ℝ) ^ n := by
    unfold successProb
    rw [inv_mul_eq_div, div_le_iff₀ hcount, add_mul, div_mul_cancel₀ _ hcount.ne']
    simpa [QAlgorithms.probEvent, Finset.sum_filter, QAlgorithms.prob, QAlgorithms.ket,
      EuclideanSpace.inner_single_left, amp, he] using hsum
  constructor
  · have hfree : 0 ≤ Efree.card / (Fintype.card X : ℝ) ^ n := by positivity
    calc _ ≤ c + Efree.card / (Fintype.card X : ℝ) ^ n := hsuccess
      _ ≤ 2 * c + 2 * (Efree.card / (Fintype.card X : ℝ) ^ n) := by linarith
      _ = _ := by dsimp [c]; ring
  · rintro rfl
    simpa [c] using hsuccess

end QNoiseStab
end
end

section
open QNoiseStab

set_option linter.unusedVariables false in
theorem solution :
    ∀ {X Ŷ W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
        {n d T : ℕ} [NeZero d] (enc : X ≃ ZMod d) (ω : ℂ) (hω : ω ^ d = 1)
        (R : Set ((Fin n → X) × Ŷ)) (A : Finset (Fin n)) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
        (Efree : Finset (Fin n → X)) (hT : T ≤ n) (alg : QAlgorithms.QueryAlg (Fin n) (ZMod d) W T)
        (out : (Fin n × ZMod d) × W → Ŷ) (β : ℝ) (hβ0 : 0 ≤ β)
        (hβ : ∀ y : Ŷ, ∀ x ∈ eventSet Efree R y, noiseProb p A x (eventSet Efree R y) ≤ β),
      successProb enc ω alg out R ≤
          2 * ((1 - p) ^ T)⁻¹ * β + 2 * (Efree.card : ℝ) / (Fintype.card X : ℝ) ^ n ∧
        (Efree = ∅ → successProb enc ω alg out R ≤ ((1 - p) ^ T)⁻¹ * β) :=
  @QNoiseStab.submission_proof

end
