-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P05.weylCalculus
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:24:55.910391+00:00
-- url     : https://prove2.me/submissions/a6ebf6d5-da57-402e-9afc-925b3421e269

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P05
noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P05

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P34 (cyclicPhase weyl dephasing)
open QAlgorithms.Papers.Independent.Gap48.P36 (WeylLabel)
open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {d : ℕ} [NeZero d]

theorem s110w_cp (x : ZMod d) : cyclicPhase d x = ZMod.stdAddChar x := by
  unfold cyclicPhase
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]

theorem s110w_cp_add (x y : ZMod d) : cyclicPhase d (x + y) = cyclicPhase d x * cyclicPhase d y := by
  simp only [s110w_cp, AddChar.map_add_eq_mul]

theorem s110w_cp_zero : cyclicPhase d 0 = 1 := by
  simp only [s110w_cp, AddChar.map_zero_eq_one]

theorem s110w_cp_neg_mul (x : ZMod d) : cyclicPhase d (-x) * cyclicPhase d x = 1 := by
  rw [← s110w_cp_add, neg_add_cancel, s110w_cp_zero]

theorem s110w_cp_conj (x : ZMod d) : star (cyclicPhase d x) = cyclicPhase d (-x) := by
  have h1 : star (cyclicPhase d x) * cyclicPhase d x = 1 := by
    unfold cyclicPhase
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    convert Complex.exp_zero
    rw [map_div₀, map_mul, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, map_natCast,
      map_natCast, map_ofNat]
    ring
  have h2 := s110w_cp_neg_mul x
  have hne : cyclicPhase d x ≠ 0 := by unfold cyclicPhase; exact Complex.exp_ne_zero _
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

theorem s110w_shift_pow (k : ℕ) (X Y : ZMod d) :
    ((Matrix.of fun a b : ZMod d => if a = b + 1 then (1:ℂ) else 0) ^ k) X Y =
      if X = Y + (k : ZMod d) then 1 else 0 := by
  induction k generalizing X Y with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp only [ih, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single (Y + 1)]
    · simp only [if_true]; push_cast; congr 1; apply propext; constructor <;> intro h <;> rw [h] <;> ring
    · intro c _ hc; simp [hc]
    · simp

theorem s110w_cp_pow (y : ZMod d) (k : ℕ) : cyclicPhase d y ^ k = cyclicPhase d ((k : ZMod d) * y) := by
  simp only [s110w_cp, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]

theorem s110w_W_apply (z : WeylLabel d) (x y : ZMod d) :
    W z x y = if x = y + z.1 then cyclicPhase d (z.2 * y) else 0 := by
  unfold W weyl
  simp only [Matrix.diagonal_pow, Matrix.mul_diagonal, s110w_shift_pow,
    ZMod.natCast_zmod_val, ite_mul, one_mul, zero_mul, Pi.pow_apply, s110w_cp_pow]

theorem s110w_tr (z : WeylLabel d) :
    (W z).trace = if z = 0 then (d : ℂ) else 0 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, s110w_W_apply]
  by_cases h1 : z.1 = 0
  · simp only [h1, add_zero, if_true]
    have := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod d) ℂ)) z.2
      (ZMod.isPrimitive_stdAddChar d)
    simp only [s110w_cp, mul_comm z.2]
    rw [this, ZMod.card]
    by_cases h2 : z.2 = 0
    · have : z = 0 := Prod.ext h1 h2
      simp [h2, this]
    · have : z ≠ 0 := fun h => h2 (by rw [h]; rfl)
      simp [h2, this]
  · have : z ≠ 0 := fun h => h1 (by rw [h]; rfl)
    rw [if_neg this]
    apply Finset.sum_eq_zero
    intro y _
    rw [if_neg]
    intro h
    apply h1
    have := congrArg (· - y) h
    simpa using this.symm


theorem s110w_mul (z v : WeylLabel d) : W z * W v = cyclicPhase d (z.2 * v.1) • W (z + v) := by
  ext x y
  rw [Matrix.mul_apply, Matrix.smul_apply, s110w_W_apply (z + v)]
  simp only [s110w_W_apply]
  rw [Finset.sum_eq_single (y + v.1)]
  · simp only [if_true, Prod.fst_add, Prod.snd_add]
    by_cases h : x = y + v.1 + z.1
    · rw [if_pos h, if_pos (by rw [h]; ring), smul_eq_mul, ← s110w_cp_add, ← s110w_cp_add]
      congr 1; ring
    · rw [if_neg h, if_neg (by rw [← add_assoc, add_right_comm]; exact h)]; simp
  · intro c _ hc; simp [hc]
  · simp

theorem s110w_star (z : WeylLabel d) : (W z)ᴴ = cyclicPhase d (z.2 * z.1) • W (-z) := by
  ext x y
  rw [Matrix.conjTranspose_apply, Matrix.smul_apply, s110w_W_apply, s110w_W_apply]
  simp only [Prod.fst_neg, Prod.snd_neg]
  by_cases h : y = x + z.1
  · rw [if_pos h, if_pos (by rw [h]; ring), smul_eq_mul, s110w_cp_conj, ← s110w_cp_add, h]
    congr 1; ring
  · rw [if_neg h, if_neg (by intro h'; apply h; rw [h']; ring)]; simp

theorem s110w_tr_mul (z v : WeylLabel d) :
    (W z * (W v)ᴴ).trace = if z = v then (d : ℂ) else 0 := by
  rw [s110w_star, Matrix.mul_smul, s110w_mul, Matrix.trace_smul, Matrix.trace_smul, s110w_tr]
  by_cases h : z = v
  · subst h
    simp only [add_neg_cancel, if_true, smul_eq_mul, Prod.snd_neg]
    rw [← mul_assoc, ← s110w_cp_add]
    rw [Prod.fst_neg, show z.2 * z.1 + z.2 * -z.1 = 0 by ring, s110w_cp_zero, one_mul]
  · rw [if_neg (by rw [← sub_eq_add_neg]; exact sub_ne_zero.mpr h), if_neg h]; simp

theorem s110w_W0 : W (0 : WeylLabel d) = 1 := by
  ext x y
  rw [s110w_W_apply, Matrix.one_apply]
  simp [s110w_cp_zero]

theorem s110w_trXW (X : Op (ZMod d)) (z : WeylLabel d) :
    (X * (W z)ᴴ).trace = ∑ w, X (w + z.1) w * cyclicPhase d (-(z.2 * w)) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, s110w_W_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_eq_single (w + z.1)]
  · simp [s110w_cp_conj]
  · intro c _ hc; simp [hc]
  · simp

theorem s110w_charsum (c : ZMod d) : ∑ b : ZMod d, cyclicPhase d (b * c) = if c = 0 then (d : ℂ) else 0 := by
  simp only [s110w_cp]
  rw [AddChar.sum_mulShift c (ZMod.isPrimitive_stdAddChar d), ZMod.card]
  split_ifs <;> simp

theorem s110w_expand (X : Op (ZMod d)) : X = ∑ z, weylFourierCoefficient X z • W z := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  ext x y
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, weylFourierCoefficient, s110w_trXW, s110w_W_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp only
  rw [Finset.sum_eq_single (x - y)]
  · rw [show y + (x - y) = x by ring]
    simp only [if_true]
    simp only [div_mul_eq_mul_div, Finset.sum_mul]
    rw [← Finset.sum_div, Finset.sum_comm]
    simp only [mul_assoc, ← s110w_cp_add, ← Finset.mul_sum]
    have : ∀ w : ZMod d, ∑ b : ZMod d, cyclicPhase d (-(b * w) + b * y) =
        if y - w = 0 then (d : ℂ) else 0 := by
      intro w; rw [← s110w_charsum]; congr 1; funext b; congr 1; ring
    simp only [this, mul_ite, mul_zero]
    rw [Finset.sum_eq_single y]
    · simp only [sub_self, if_true]
      rw [show y + (x - y) = x by ring]; field_simp
    · intro w _ hw; rw [if_neg (sub_ne_zero.mpr (Ne.symm hw))]
    · simp
  · intro a _ ha
    apply Finset.sum_eq_zero; intro b _
    rw [if_neg (by intro h; apply ha; rw [h]; ring)]; simp
  · simp


theorem s110w_trstar (X : Op (ZMod d)) (z : WeylLabel d) :
    (Xᴴ * W z).trace = star ((X * (W z)ᴴ).trace) := by
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.trace_mul_comm]

theorem s110w_parseval (X : Op (ZMod d)) :
    (Xᴴ * X).trace = (((d : ℝ) * ∑ z, ‖weylFourierCoefficient X z‖ ^ 2 : ℝ) : ℂ) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hX := s110w_expand X
  calc (Xᴴ * X).trace = (Xᴴ * ∑ z, weylFourierCoefficient X z • W z).trace := by rw [← hX]
    _ = _ := by
      rw [Matrix.mul_sum, Matrix.trace_sum]
      simp only [Matrix.mul_smul, Matrix.trace_smul, s110w_trstar, smul_eq_mul]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      have : (X * (W z)ᴴ).trace = (d : ℂ) * weylFourierCoefficient X z := by
        unfold weylFourierCoefficient; field_simp
      rw [this, star_mul', Complex.star_def, Complex.conj_natCast, ← Complex.mul_conj']
      ring

theorem s110w_conj (X : Op (ZMod d)) (z : WeylLabel d) :
    conj (weylFourierCoefficient X z) =
      cyclicPhase d (-(z.2 * z.1)) * weylFourierCoefficient Xᴴ (-z) := by
  unfold weylFourierCoefficient
  rw [s110w_star (-z), Matrix.mul_smul, Matrix.trace_smul, map_div₀, Complex.conj_natCast,
    ← Complex.star_def, ← s110w_trstar]
  simp only [Prod.fst_neg, Prod.snd_neg, neg_neg, smul_eq_mul]
  rw [← mul_div_assoc, ← mul_assoc, ← s110w_cp_add, show -(z.2 * z.1) + -z.2 * -z.1 = 0 by ring,
    s110w_cp_zero, one_mul]

end QAlgorithms.Papers.Independent.Bridge50.P05

open QAlgorithms.Papers.Independent.Bridge50.P05
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Information100.P34 (cyclicPhase weyl dephasing)
open QAlgorithms.Papers.Independent.Gap48.P36 (WeylLabel)
open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {d : ℕ} [NeZero d] (X : Op (ZMod d)) :
    (∀ z v : WeylLabel d, W z * W v = cyclicPhase d (z.2 * v.1) • W (z + v)) ∧
    (∀ z v : WeylLabel d, W z * W v =
      cyclicPhase d (v.1 * z.2 - v.2 * z.1) • (W v * W z)) ∧
    (∀ z : WeylLabel d, (W z)ᴴ = cyclicPhase d (z.2 * z.1) • W (-z)) ∧
    (∀ z v : WeylLabel d, (W z * (W v)ᴴ).trace = if z = v then (d : ℂ) else 0) ∧
    X = ∑ z, weylFourierCoefficient X z • W z ∧
    X.trace = (d : ℂ) * weylFourierCoefficient X 0 ∧
    (Xᴴ * X).trace = (((d : ℝ) * ∑ z, ‖weylFourierCoefficient X z‖ ^ 2 : ℝ) : ℂ) ∧
    (∀ z : WeylLabel d, conj (weylFourierCoefficient X z) =
      cyclicPhase d (-(z.2 * z.1)) * weylFourierCoefficient Xᴴ (-z)) := by
  refine ⟨s110w_mul, ?_, s110w_star, s110w_tr_mul, s110w_expand X, ?_, s110w_parseval X, s110w_conj X⟩
  · intro z v
    rw [s110w_mul, s110w_mul, smul_smul, ← s110w_cp_add, add_comm v z]
    congr 2; ring
  · have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    unfold weylFourierCoefficient
    rw [s110w_W0, Matrix.conjTranspose_one, Matrix.mul_one]
    field_simp
