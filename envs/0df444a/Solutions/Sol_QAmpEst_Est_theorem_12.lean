-- Prove2me | solution 1 for QAmpEst.Est.theorem_12
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-26T14:01:13.6278+00:00
-- url     : https://prove2.me/submissions/f55c9156-8f66-4850-8627-eea589fafe2e

-- SPDX-License-Identifier: Apache-2.0

import Definitions.Def_QAmpEst_Est_Fourier
import Definitions.Def_QAmpEst_Est_Setting
import Mathlib

open scoped Real Kronecker


section

namespace QAmpEst.Est.AEFresh
open scoped ComplexConjugate
open Matrix

variable {ι : Type*} [Fintype ι]

noncomputable def normSum (v : ι → ℂ) : ℝ := ∑ i, Complex.normSq (v i)
noncomputable def innerSum (u v : ι → ℂ) : ℂ := ∑ i, conj (u i) * v i

theorem normSum_nonneg (v : ι → ℂ) : 0 ≤ normSum v :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem coe_normSum (v : ι → ℂ) : (normSum v : ℂ) = innerSum v v := by
  simp [normSum, innerSum, Complex.normSq_eq_conj_mul_self]

theorem innerSum_add_right (u v w : ι → ℂ) :
    innerSum u (v + w) = innerSum u v + innerSum u w := by
  simp [innerSum, mul_add, Finset.sum_add_distrib]

theorem innerSum_smul_right (u v : ι → ℂ) (c : ℂ) :
    innerSum u (c • v) = c * innerSum u v := by
  simp only [innerSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  ext i
  ring

theorem innerSum_conj_symm (u v : ι → ℂ) :
    conj (innerSum u v) = innerSum v u := by
  simp [innerSum, map_sum, mul_comm]

theorem innerSum_add_left (u v w : ι → ℂ) :
    innerSum (u + v) w = innerSum u w + innerSum v w := by
  simp [innerSum, add_mul, Finset.sum_add_distrib]

theorem innerSum_smul_left (u v : ι → ℂ) (c : ℂ) :
    innerSum (c • u) v = conj c * innerSum u v := by
  simp [innerSum, mul_assoc, Finset.mul_sum]

theorem normSum_smul (c : ℂ) (v : ι → ℂ) :
    normSum (c • v) = Complex.normSq c * normSum v := by
  simp [normSum, Complex.normSq_mul, Finset.mul_sum]

theorem normSum_add_of_orthogonal (u v : ι → ℂ) (h : innerSum u v = 0) :
    normSum (u + v) = normSum u + normSum v := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_add, coe_normSum, coe_normSum, coe_normSum,
    innerSum_add_left, innerSum_add_right, innerSum_add_right, h]
  have hv : innerSum v u = 0 := by rw [← innerSum_conj_symm, h, map_zero]
  rw [hv]
  ring

theorem normSum_linear_orthogonal (u v : ι → ℂ) (h : innerSum u v = 0) (a b : ℂ) :
    normSum (a • u + b • v) = Complex.normSq a * normSum u +
      Complex.normSq b * normSum v := by
  rw [normSum_add_of_orthogonal, normSum_smul, normSum_smul]
  rw [innerSum_smul_left, innerSum_smul_right, h, mul_zero, mul_zero]

end QAmpEst.Est.AEFresh
end


section

namespace QAmpEst.Est.AEFresh
open scoped ComplexConjugate
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem initState_apply (A : Matrix ι ι ℂ) (z0 i : ι) : initState A z0 i = A i z0 := by
  simp [initState, Matrix.mulVec_single]

theorem normSum_init (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ) (z0 : ι) :
    normSum (initState A z0) = 1 := by
  apply Complex.ofReal_injective
  rw [coe_normSum]
  have h := congrArg (fun B : Matrix ι ι ℂ => B z0 z0)
    (Matrix.mem_unitaryGroup_iff'.mp hA)
  simpa [innerSum, initState_apply, Matrix.mul_apply, Matrix.star_apply] using h

omit [Fintype ι] [DecidableEq ι] in
theorem good_add_bad (χ : ι → Bool) (v : ι → ℂ) : goodPart χ v + badPart χ v = v := by
  ext i
  cases h : χ i <;> simp [goodPart, badPart, h]

omit [DecidableEq ι] in
theorem normSum_good (χ : ι → Bool) (v : ι → ℂ) :
    normSum (goodPart χ v) = goodProb χ v := by
  unfold normSum goodProb
  apply Finset.sum_congr rfl
  intro i _
  cases h : χ i <;> simp [goodPart, h]

omit [DecidableEq ι] in
theorem good_bad_orthogonal (χ : ι → Bool) (v : ι → ℂ) :
    innerSum (goodPart χ v) (badPart χ v) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  cases h : χ i <;> simp [goodPart, badPart, h]

omit [DecidableEq ι] in
theorem innerSum_good (χ : ι → Bool) (v : ι → ℂ) :
    innerSum v (goodPart χ v) = (goodProb χ v : ℂ) := by
  conv_lhs => arg 1; rw [← good_add_bad χ v]
  rw [innerSum_add_left]
  have h : innerSum (badPart χ v) (goodPart χ v) = 0 := by
    rw [← innerSum_conj_symm, good_bad_orthogonal, map_zero]
  rw [h, add_zero, ← coe_normSum, normSum_good]

theorem succProb_bounds (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ)
    (χ : ι → Bool) (z0 : ι) : 0 ≤ succProb A χ z0 ∧ succProb A χ z0 ≤ 1 := by
  have hg := normSum_nonneg (goodPart χ (initState A z0))
  have hb := normSum_nonneg (badPart χ (initState A z0))
  have he := normSum_add_of_orthogonal _ _ (good_bad_orthogonal χ (initState A z0))
  rw [good_add_bad, normSum_init A hA, normSum_good] at he
  rw [normSum_good] at hg
  exact ⟨hg, by dsimp [succProb]; linarith⟩

theorem normSum_bad_init (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ)
    (χ : ι → Bool) (z0 : ι) :
    normSum (badPart χ (initState A z0)) = 1 - succProb A χ z0 := by
  have he := normSum_add_of_orthogonal _ _ (good_bad_orthogonal χ (initState A z0))
  rw [good_add_bad, normSum_init A hA, normSum_good] at he
  dsimp [succProb]
  linarith

theorem innerSum_bad_init (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ)
    (χ : ι → Bool) (z0 : ι) :
    innerSum (initState A z0) (badPart χ (initState A z0)) =
      ((1 - succProb A χ z0 : ℝ) : ℂ) := by
  conv_lhs => arg 1; rw [← good_add_bad χ (initState A z0)]
  rw [innerSum_add_left, good_bad_orthogonal, zero_add, ← coe_normSum, normSum_bad_init A hA]

end QAmpEst.Est.AEFresh
end


section

namespace QAmpEst.Est.AEFresh
open scoped ComplexConjugate
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem signZero_action (z0 : ι) (v : ι → ℂ) :
    (signZero z0).mulVec v = v - (2 * v z0) • Pi.single z0 1 := by
  ext i
  by_cases h : i = z0
  · subst i
    simp [signZero, Matrix.mulVec_diagonal]
    ring
  · simp [signZero, Matrix.mulVec_diagonal, h]

theorem signGood_good (χ : ι → Bool) (v : ι → ℂ) :
    (signGood χ).mulVec (goodPart χ v) = -goodPart χ v := by
  ext i
  cases h : χ i <;> simp [signGood, Matrix.mulVec_diagonal, goodPart, h]

theorem signGood_bad (χ : ι → Bool) (v : ι → ℂ) :
    (signGood χ).mulVec (badPart χ v) = badPart χ v := by
  ext i
  cases h : χ i <;> simp [signGood, Matrix.mulVec_diagonal, badPart, h]

theorem star_init_inner (A : Matrix ι ι ℂ) (z0 : ι) (v : ι → ℂ) :
    (star A).mulVec v z0 = innerSum (initState A z0) v := by
  simp [Matrix.mulVec, dotProduct, innerSum, initState_apply, Matrix.star_apply]

theorem conjugate_reflection_action (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (z0 : ι) (v : ι → ℂ) :
    (A * signZero z0 * star A).mulVec v =
      v - (2 * innerSum (initState A z0) v) • initState A z0 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, signZero_action,
    Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [Matrix.mulVec_mulVec, Matrix.mem_unitaryGroup_iff.mp hA, Matrix.one_mulVec,
    star_init_inner]
  rfl

theorem Qop_action (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ)
    (χ : ι → Bool) (z0 : ι) (v : ι → ℂ) :
    (Qop A χ z0).mulVec v =
      (2 * innerSum (initState A z0) ((signGood χ).mulVec v)) • initState A z0 -
        (signGood χ).mulVec v := by
  rw [Qop, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec,
    conjugate_reflection_action A hA]
  simp only [neg_sub]

theorem Qop_good (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ)
    (χ : ι → Bool) (z0 : ι) :
    (Qop A χ z0).mulVec (goodPart χ (initState A z0)) =
      (1 - 2 * (succProb A χ z0 : ℂ)) • goodPart χ (initState A z0) -
      (2 * (succProb A χ z0 : ℂ)) • badPart χ (initState A z0) := by
  rw [Qop_action A hA, signGood_good]
  have hn : innerSum (initState A z0) (-goodPart χ (initState A z0)) =
      -(succProb A χ z0 : ℂ) := by
    rw [← neg_one_smul ℂ (goodPart χ (initState A z0)), innerSum_smul_right, innerSum_good]
    simp [succProb]
  rw [hn]
  conv_lhs => arg 1; arg 2; rw [← good_add_bad χ (initState A z0)]
  ext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  ring

theorem Qop_bad (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ)
    (χ : ι → Bool) (z0 : ι) :
    (Qop A χ z0).mulVec (badPart χ (initState A z0)) =
      (2 * (1 - (succProb A χ z0 : ℂ))) • goodPart χ (initState A z0) +
      (1 - 2 * (succProb A χ z0 : ℂ)) • badPart χ (initState A z0) := by
  rw [Qop_action A hA, signGood_bad, innerSum_bad_init A hA,
    Complex.ofReal_sub, Complex.ofReal_one]
  conv_lhs => arg 1; arg 2; rw [← good_add_bad χ (initState A z0)]
  ext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  ring

end QAmpEst.Est.AEFresh
end


section

namespace QAmpEst.Est.AEFresh
open scoped Real

theorem theta_facts {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    0 ≤ theta a ∧ theta a ≤ π / 2 ∧ Real.sin (theta a) = Real.sqrt a ∧
      Real.cos (theta a) = Real.sqrt (1-a) := by
  have hs : Real.sqrt a ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact ha1
  refine ⟨Real.arcsin_nonneg.mpr (Real.sqrt_nonneg a), Real.arcsin_le_pi_div_two _, ?_, ?_⟩
  · exact Real.sin_arcsin (by linarith [Real.sqrt_nonneg a]) hs
  · rw [theta, Real.cos_arcsin, Real.sq_sqrt ha]

theorem theta_sin_sq {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.sin (theta a) ^ 2 = a := by
  rw [(theta_facts ha ha1).2.2.1, Real.sq_sqrt ha]

theorem double_theta_cos {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.cos (2 * theta a) = 1 - 2*a := by
  rw [Real.cos_two_mul, (theta_facts ha ha1).2.2.2, Real.sq_sqrt (by linarith : 0 ≤ 1-a)]
  ring

theorem double_theta_sin {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.sin (2 * theta a) = 2 * Real.sqrt a * Real.sqrt (1-a) := by
  rw [Real.sin_two_mul, (theta_facts ha ha1).2.2.1, (theta_facts ha ha1).2.2.2]

theorem exp_double_theta {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Complex.exp ((2 * theta a : ℝ) * Complex.I) =
      (1 - 2*a : ℝ) + (2 * Real.sqrt a * Real.sqrt (1-a) : ℝ) * Complex.I := by
  rw [Complex.exp_ofReal_mul_I, double_theta_cos ha ha1, double_theta_sin ha ha1]

end QAmpEst.Est.AEFresh
end


section

namespace QAmpEst.Est.AEFresh
open scoped ComplexConjugate
open Matrix
variable {ι : Type*} [Fintype ι]

theorem normalize_rotation (U : Matrix ι ι ℂ) (g b : ι → ℂ) (a s t : ℂ)
    (hs : s ≠ 0) (ht : t ≠ 0) (hss : s*s=a) (htt : t*t=1-a)
    (hg : U.mulVec g = (1-2*a) • g - (2*a) • b)
    (hb : U.mulVec b = (2*(1-a)) • g + (1-2*a) • b) :
    U.mulVec (s⁻¹ • g) = (1-2*a) • (s⁻¹ • g) - (2*s*t) • (t⁻¹ • b) ∧
    U.mulVec (t⁻¹ • b) = (2*s*t) • (s⁻¹ • g) + (1-2*a) • (t⁻¹ • b) := by
  constructor
  · rw [Matrix.mulVec_smul, hg]
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [← hss]
    field_simp
  · rw [Matrix.mulVec_smul, hb]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [← htt]
    field_simp

noncomputable def normalizedGood [DecidableEq ι] (A : Matrix ι ι ℂ) (χ : ι → Bool)
    (z0 : ι) : ι → ℂ :=
  (Real.sqrt (succProb A χ z0) : ℂ)⁻¹ • goodPart χ (initState A z0)

noncomputable def normalizedBad [DecidableEq ι] (A : Matrix ι ι ℂ) (χ : ι → Bool)
    (z0 : ι) : ι → ℂ :=
  (Real.sqrt (1-succProb A χ z0) : ℂ)⁻¹ • badPart χ (initState A z0)

variable [DecidableEq ι]

theorem normalized_geometry (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ)
    (χ : ι → Bool) (z0 : ι) (ha : 0 < succProb A χ z0) (ha1 : succProb A χ z0 < 1) :
    normSum (normalizedGood A χ z0) = 1 ∧ normSum (normalizedBad A χ z0) = 1 ∧
      innerSum (normalizedGood A χ z0) (normalizedBad A χ z0) = 0 := by
  have hna := ne_of_gt ha
  have hnb : 1-succProb A χ z0 ≠ 0 := by linarith
  constructor
  · rw [normalizedGood, normSum_smul, normSum_good, Complex.normSq_inv,
      Complex.normSq_ofReal, Real.mul_self_sqrt ha.le]
    exact inv_mul_cancel₀ hna
  constructor
  · rw [normalizedBad, normSum_smul, normSum_bad_init A hA, Complex.normSq_inv,
      Complex.normSq_ofReal, Real.mul_self_sqrt (by linarith)]
    exact inv_mul_cancel₀ hnb
  · rw [normalizedGood, normalizedBad, innerSum_smul_left, innerSum_smul_right,
      good_bad_orthogonal, mul_zero, mul_zero]

theorem normalized_initial (A : Matrix ι ι ℂ) (χ : ι → Bool) (z0 : ι)
    (ha : 0 < succProb A χ z0) (ha1 : succProb A χ z0 < 1) :
    initState A z0 = (Real.sqrt (succProb A χ z0) : ℂ) • normalizedGood A χ z0 +
      (Real.sqrt (1-succProb A χ z0) : ℂ) • normalizedBad A χ z0 := by
  have hs : (Real.sqrt (succProb A χ z0) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr ha)
  have ht : (Real.sqrt (1-succProb A χ z0) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by linarith : 0 < 1-succProb A χ z0))
  rw [normalizedGood, normalizedBad, smul_smul, smul_smul,
    mul_inv_cancel₀ hs, mul_inv_cancel₀ ht, one_smul, one_smul, good_add_bad]

theorem normalized_rotation (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ)
    (χ : ι → Bool) (z0 : ι) (ha : 0 < succProb A χ z0) (ha1 : succProb A χ z0 < 1) :
    (Qop A χ z0).mulVec (normalizedGood A χ z0) =
      (Real.cos (2*theta (succProb A χ z0)) : ℂ) • normalizedGood A χ z0 -
      (Real.sin (2*theta (succProb A χ z0)) : ℂ) • normalizedBad A χ z0 ∧
    (Qop A χ z0).mulVec (normalizedBad A χ z0) =
      (Real.sin (2*theta (succProb A χ z0)) : ℂ) • normalizedGood A χ z0 +
      (Real.cos (2*theta (succProb A χ z0)) : ℂ) • normalizedBad A χ z0 := by
  rw [double_theta_cos ha.le ha1.le, double_theta_sin ha.le ha1.le]
  push_cast
  apply normalize_rotation _ _ _ _ _ _ _ _ _ _ (Qop_good A hA χ z0) (Qop_bad A hA χ z0)
  · exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr ha)
  · exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by linarith : 0 < 1-succProb A χ z0))
  · exact_mod_cast Real.mul_self_sqrt ha.le
  · exact_mod_cast Real.mul_self_sqrt (by linarith : 0 ≤ 1-succProb A χ z0)

end QAmpEst.Est.AEFresh
end


section

namespace QAmpEst.Est.AEFresh
open scoped Kronecker
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def inputVec (M : ℕ) (v : ι → ℂ) : Fin M × ι → ℂ :=
  fun p => if (p.1 : ℕ) = 0 then v p.2 else 0

noncomputable def circuitVec (M : ℕ) (U : Matrix ι ι ℂ) (v : ι → ℂ) : Fin M × ι → ℂ :=
  ((qftInv M ⊗ₖ (1 : Matrix ι ι ℂ)) * ctrlPow M U *
    (ShorAlgorithms.Shared.fourierMatrix M ⊗ₖ (1 : Matrix ι ι ℂ))).mulVec (inputVec M v)

theorem kronecker_one_action {M : ℕ} (B : Matrix (Fin M) (Fin M) ℂ)
    (f : Fin M × ι → ℂ) (y : Fin M) (z : ι) :
    (B ⊗ₖ (1 : Matrix ι ι ℂ)).mulVec f (y,z) = ∑ j, B y j * f (j,z) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]

theorem controlled_action {M : ℕ} (U : Matrix ι ι ℂ) (f : Fin M × ι → ℂ)
    (j : Fin M) (z : ι) :
    (ctrlPow M U).mulVec f (j,z) = (U ^ (j : ℕ)).mulVec (fun x => f (j,x)) z := by
  simp [ctrlPow, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

theorem fourier_input_action (M : ℕ) (hM : 0 < M) (v : ι → ℂ) (j : Fin M) (z : ι) :
    (ShorAlgorithms.Shared.fourierMatrix M ⊗ₖ (1 : Matrix ι ι ℂ)).mulVec
      (inputVec M v) (j,z) = (Real.sqrt M : ℂ)⁻¹ * v z := by
  rw [kronecker_one_action]
  rw [Finset.sum_eq_single (⟨0,hM⟩ : Fin M)]
  · simp [inputVec, ShorAlgorithms.Shared.fourierMatrix]
  · intro b _ hb
    have h : (b : ℕ) ≠ 0 := fun he => hb (Fin.ext he)
    simp [inputVec, h]
  · simp

theorem circuitVec_expand (M : ℕ) (hM : 0 < M) (U : Matrix ι ι ℂ)
    (v : ι → ℂ) (y : Fin M) (z : ι) :
    circuitVec M U v (y,z) = (Real.sqrt M : ℂ)⁻¹ *
      ∑ j : Fin M, qftInv M y j * (U ^ (j : ℕ)).mulVec v z := by
  unfold circuitVec
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, kronecker_one_action]
  simp_rw [controlled_action, fourier_input_action M hM]
  have he (j : Fin M) :
      (U ^ (j : ℕ)).mulVec (fun x => (Real.sqrt M : ℂ)⁻¹ * v x) =
        (Real.sqrt M : ℂ)⁻¹ • (U ^ (j : ℕ)).mulVec v := by
    exact Matrix.mulVec_smul (U ^ (j : ℕ)) ((Real.sqrt M : ℂ)⁻¹) v
  simp_rw [he, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem pow_mulVec_eigen (U : Matrix ι ι ℂ) (v : ι → ℂ) (lam : ℂ)
    (hv : U.mulVec v = lam • v) (n : ℕ) : (U ^ n).mulVec v = lam ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hv, smul_smul, pow_succ]

noncomputable def eigenResponse (M : ℕ) (lam : ℂ) (y : Fin M) : ℂ :=
  (Real.sqrt M : ℂ)⁻¹ * ∑ j : Fin M, qftInv M y j * lam ^ (j : ℕ)

theorem circuitVec_eigen (M : ℕ) (hM : 0 < M) (U : Matrix ι ι ℂ) (v : ι → ℂ)
    (lam : ℂ) (hv : U.mulVec v = lam • v) (y : Fin M) (z : ι) :
    circuitVec M U v (y,z) = eigenResponse M lam y * v z := by
  rw [circuitVec_expand M hM]
  simp_rw [pow_mulVec_eigen U v lam hv, Pi.smul_apply, smul_eq_mul]
  simp only [eigenResponse, mul_assoc, Finset.sum_mul]

theorem circuitVec_add (M : ℕ) (U : Matrix ι ι ℂ) (u v : ι → ℂ) :
    circuitVec M U (u+v) = circuitVec M U u + circuitVec M U v := by
  have he : inputVec M (u+v) = inputVec M u + inputVec M v := by
    ext p
    by_cases h : (p.1 : ℕ) = 0 <;> simp [inputVec, h]
  simp only [circuitVec, he, Matrix.mulVec_add]

theorem circuitVec_smul (M : ℕ) (U : Matrix ι ι ℂ) (v : ι → ℂ) (c : ℂ) :
    circuitVec M U (c • v) = c • circuitVec M U v := by
  have he : inputVec M (c • v) = c • inputVec M v := by
    ext p
    by_cases h : (p.1 : ℕ) = 0 <;> simp [inputVec, h]
  simp only [circuitVec, he, Matrix.mulVec_smul]

theorem estAmpState_eq_circuitVec (M : ℕ) (A : Matrix ι ι ℂ) (χ : ι → Bool) (z0 : ι) :
    estAmpState M A χ z0 = circuitVec M (Qop A χ z0) (initState A z0) := rfl

end QAmpEst.Est.AEFresh
end


section

noncomputable section
open scoped Real
namespace QAmpEst.Est.AEFresh

def phaseExp (t : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * (t : ℂ))

theorem phaseExp_add (s t : ℝ) : phaseExp (s + t) = phaseExp s * phaseExp t := by
  simp only [phaseExp, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem phaseExp_zero : phaseExp 0 = 1 := by simp [phaseExp]

theorem phaseExp_int (z : ℤ) : phaseExp z = 1 := by
  apply Complex.exp_eq_one_iff.mpr
  exact ⟨z, by dsimp [phaseExp]; ring⟩

theorem phaseExp_add_int (t : ℝ) (z : ℤ) : phaseExp (t + z) = phaseExp t := by
  rw [phaseExp_add, phaseExp_int, mul_one]

theorem phaseExp_conj (t : ℝ) : star (phaseExp t) = phaseExp (-t) := by
  simp only [phaseExp, Complex.star_def, ← Complex.exp_conj, map_mul,
    map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  congr 1
  norm_num

theorem qftInv_entry (M : ℕ) (x y : Fin M) :
    qftInv M x y = (Real.sqrt M : ℂ)⁻¹ *
      phaseExp (-((x : ℕ) : ℝ) * (y : ℕ) / M) := by
  change star ((Real.sqrt M : ℂ)⁻¹ *
    Complex.exp (2 * π * Complex.I * ((y : ℕ) : ℂ) * ((x : ℕ) : ℂ) / (M : ℂ))) = _
  have he : Complex.exp (2 * π * Complex.I * ((y : ℕ) : ℂ) *
      ((x : ℕ) : ℂ) / (M : ℂ)) = phaseExp (((y : ℕ) : ℝ) * (x : ℕ) / M) := by
    unfold phaseExp
    congr 1
    push_cast
    ring
  rw [he, star_mul, phaseExp_conj]
  simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have ha : -(((y : ℕ) : ℝ) * (x : ℕ) / M) = -((x : ℕ) : ℝ) * (y : ℕ) / M := by ring
  rw [ha]
  ring

def phaseAmplitude (M : ℕ) (ω : ℝ) (y : Fin M) : ℂ :=
  (M : ℂ)⁻¹ * ∑ j : Fin M, phaseExp ((ω - (y : ℕ) / M) * (j : ℕ))

theorem inverseQFT_stateS (M : ℕ) (ω : ℝ) (y : Fin M) :
    (qftInv M).mulVec (stateS M ω) y = phaseAmplitude M ω y := by
  have hs : (Real.sqrt M : ℂ) * (Real.sqrt M : ℂ) = (M : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (Nat.cast_nonneg M)
  unfold Matrix.mulVec dotProduct phaseAmplitude
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change qftInv M y j * stateS M ω j = _
  rw [qftInv_entry]
  have he : stateS M ω j = phaseExp (ω * (j : ℕ)) / (Real.sqrt M : ℂ) := by
    unfold stateS phaseExp
    congr 1
    push_cast
    ring
  rw [he, div_eq_mul_inv]
  have hp := phaseExp_add (-((y : ℕ) : ℝ) * (j : ℕ) / M) (ω * (j : ℕ))
  have ha : -((y : ℕ) : ℝ) * (j : ℕ) / M + ω * (j : ℕ) =
      (ω - (y : ℕ) / M) * (j : ℕ) := by ring
  rw [ha] at hp
  rw [← hs, mul_inv_rev, hp]
  ring

theorem phaseProb_eq_normSq (M : ℕ) (ω : ℝ) (y : Fin M) :
    phaseProb M ω y = Complex.normSq (phaseAmplitude M ω y) := by
  rw [phaseProb, inverseQFT_stateS M]

end QAmpEst.Est.AEFresh
end
end


section

namespace QAmpEst.Est.AEFresh
open scoped Real
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem phaseExp_pow (ω : ℝ) (j : ℕ) : phaseExp ω ^ j = phaseExp (ω*j) := by
  induction j with
  | zero => simp [phaseExp_zero]
  | succ j ih =>
    rw [pow_succ, ih, ← phaseExp_add]
    congr 1
    push_cast
    ring

theorem eigenResponse_phaseExp (M : ℕ) (ω : ℝ) (y : Fin M) :
    eigenResponse M (phaseExp ω) y = phaseAmplitude M ω y := by
  rw [← inverseQFT_stateS]
  unfold eigenResponse Matrix.mulVec dotProduct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [phaseExp_pow]
  have he : stateS M ω j = phaseExp (ω*(j:ℕ)) / (Real.sqrt M : ℂ) := by
    unfold stateS phaseExp
    congr 1
    push_cast
    ring
  change (Real.sqrt M : ℂ)⁻¹ * (qftInv M y j * phaseExp (ω*(j:ℕ))) = _
  rw [he]
  ring

theorem circuitVec_phase_eigen (M : ℕ) (hM : 0 < M) (U : Matrix ι ι ℂ)
    (v : ι → ℂ) (ω : ℝ) (hv : U.mulVec v = phaseExp ω • v) (y : Fin M) :
    (fun z => circuitVec M U v (y,z)) = phaseAmplitude M ω y • v := by
  ext z
  rw [circuitVec_eigen M hM U v _ hv, eigenResponse_phaseExp]
  rfl

theorem circuit_probability_eigen (M : ℕ) (hM : 0 < M) (U : Matrix ι ι ℂ)
    (v : ι → ℂ) (ω : ℝ) (hv : U.mulVec v = phaseExp ω • v) (y : Fin M) :
    normSum (fun z => circuitVec M U v (y,z)) = phaseProb M ω y * normSum v := by
  rw [circuitVec_phase_eigen M hM U v ω hv, normSum_smul, phaseProb_eq_normSq]

theorem circuit_probability_pair (M : ℕ) (hM : 0 < M) (U : Matrix ι ι ℂ)
    (u v : ι → ℂ) (ω η : ℝ) (hu : U.mulVec u = phaseExp ω • u)
    (hv : U.mulVec v = phaseExp η • v) (ho : innerSum u v = 0) (a b : ℂ) (y : Fin M) :
    normSum (fun z => circuitVec M U (a • u + b • v) (y,z)) =
      Complex.normSq a * phaseProb M ω y * normSum u +
      Complex.normSq b * phaseProb M η y * normSum v := by
  have he : (fun z => circuitVec M U (a • u + b • v) (y,z)) =
      (a * phaseAmplitude M ω y) • u + (b * phaseAmplitude M η y) • v := by
    ext z
    rw [circuitVec_add, circuitVec_smul, circuitVec_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [circuitVec_eigen M hM U u _ hu, circuitVec_eigen M hM U v _ hv,
      eigenResponse_phaseExp, eigenResponse_phaseExp]
    ring
  rw [he, normSum_linear_orthogonal u v ho, Complex.normSq_mul, Complex.normSq_mul,
    ← phaseProb_eq_normSq, ← phaseProb_eq_normSq]

end QAmpEst.Est.AEFresh
end


section

namespace QAmpEst.Est.AEFresh
open scoped ComplexConjugate
open Matrix
variable {ι : Type*} [Fintype ι]

theorem rotation_eigen_plus (U : Matrix ι ι ℂ) (g b : ι → ℂ) (c s : ℂ)
    (hg : U.mulVec g = c • g - s • b) (hb : U.mulVec b = s • g + c • b) :
    U.mulVec (g + Complex.I • b) = (c + s*Complex.I) • (g + Complex.I • b) := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hg, hb]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination -(s * b i) * Complex.I_sq

theorem rotation_eigen_minus (U : Matrix ι ι ℂ) (g b : ι → ℂ) (c s : ℂ)
    (hg : U.mulVec g = c • g - s • b) (hb : U.mulVec b = s • g + c • b) :
    U.mulVec (g - Complex.I • b) = (c - s*Complex.I) • (g - Complex.I • b) := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hg, hb]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination -(s * b i) * Complex.I_sq

theorem eigen_pair_geometry (g b : ι → ℂ) (hg : normSum g = 1) (hb : normSum b = 1)
    (ho : innerSum g b = 0) :
    normSum (g + Complex.I • b) = 2 ∧ normSum (g - Complex.I • b) = 2 ∧
      innerSum (g + Complex.I • b) (g - Complex.I • b) = 0 := by
  have hbg : innerSum b g = 0 := by rw [← innerSum_conj_symm, ho, map_zero]
  have hgg : innerSum g g = 1 := by rw [← coe_normSum, hg]; norm_num
  have hbb : innerSum b b = 1 := by rw [← coe_normSum, hb]; norm_num
  have hm : g - Complex.I • b = g + (-Complex.I) • b := by module
  rw [hm]
  constructor
  · rw [normSum_add_of_orthogonal, normSum_smul, hg, hb]
    · norm_num
    · rw [innerSum_smul_right, ho, mul_zero]
  constructor
  · rw [normSum_add_of_orthogonal, normSum_smul, hg, hb]
    · norm_num
    · rw [innerSum_smul_right, ho, mul_zero]
  · rw [innerSum_add_left, innerSum_add_right, innerSum_add_right,
      innerSum_smul_right, innerSum_smul_left, innerSum_smul_left,
      innerSum_smul_right, ho, hbg, hgg, hbb]
    norm_num

omit [Fintype ι] in
theorem eigen_pair_decomposition (g b : ι → ℂ) (s c : ℂ) :
    s • g + c • b = ((s-c*Complex.I)/2) • (g+Complex.I•b) +
      ((s+c*Complex.I)/2) • (g-Complex.I•b) := by
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (c * b i) * Complex.I_sq

end QAmpEst.Est.AEFresh
end


section

namespace QAmpEst.Est.AEFresh
open scoped Real ComplexConjugate
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem phaseExp_angle (θ : ℝ) : phaseExp (θ/π) =
    (Real.cos (2*θ) : ℂ) + (Real.sin (2*θ) : ℂ)*Complex.I := by
  have he : 2 * (π:ℂ) * Complex.I * ((θ/π:ℝ):ℂ) = ((2*θ:ℝ):ℂ)*Complex.I := by
    push_cast
    field_simp
  rw [phaseExp, he, Complex.exp_ofReal_mul_I]

theorem phaseExp_neg_angle (θ : ℝ) : phaseExp (-θ/π) =
    (Real.cos (2*θ) : ℂ) - (Real.sin (2*θ) : ℂ)*Complex.I := by
  rw [show -θ/π = -(θ/π) by ring, ← phaseExp_conj, phaseExp_angle]
  simp only [star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem rotation_coefficient_norm (θ : ℝ) :
    Complex.normSq (((Real.sin θ : ℂ)-(Real.cos θ : ℂ)*Complex.I)/2) = 1/4 ∧
    Complex.normSq (((Real.sin θ : ℂ)+(Real.cos θ : ℂ)*Complex.I)/2) = 1/4 := by
  have h := Real.sin_sq_add_cos_sq θ
  have hp (s c : ℝ) : Complex.normSq (((s:ℂ)+(c:ℂ)*Complex.I)/2) = (s^2+c^2)/4 := by
    rw [Complex.normSq_div, Complex.normSq_add_mul_I]
    norm_num
  have hm : ((Real.sin θ : ℂ)-(Real.cos θ : ℂ)*Complex.I)/2 =
      ((Real.sin θ : ℂ)+((-Real.cos θ:ℝ):ℂ)*Complex.I)/2 := by push_cast; ring
  rw [hm, hp, hp]
  constructor <;> nlinarith

theorem circuit_rotation_marginal (M : ℕ) (hM : 0 < M) (U : Matrix ι ι ℂ)
    (g b : ι → ℂ) (θ : ℝ) (hg : normSum g = 1) (hb : normSum b = 1)
    (ho : innerSum g b = 0)
    (hUg : U.mulVec g = (Real.cos (2*θ):ℂ) • g - (Real.sin (2*θ):ℂ) • b)
    (hUb : U.mulVec b = (Real.sin (2*θ):ℂ) • g + (Real.cos (2*θ):ℂ) • b)
    (y : Fin M) :
    normSum (fun z => circuitVec M U ((Real.sin θ:ℂ) • g + (Real.cos θ:ℂ) • b) (y,z)) =
      (phaseProb M (θ/π) y + phaseProb M (-θ/π) y)/2 := by
  have hp : U.mulVec (g+Complex.I•b) = phaseExp (θ/π) • (g+Complex.I•b) := by
    rw [phaseExp_angle]
    exact rotation_eigen_plus U g b _ _ hUg hUb
  have hm : U.mulVec (g-Complex.I•b) = phaseExp (-θ/π) • (g-Complex.I•b) := by
    rw [phaseExp_neg_angle]
    exact rotation_eigen_minus U g b _ _ hUg hUb
  have hgeom := eigen_pair_geometry g b hg hb ho
  rw [eigen_pair_decomposition g b, circuit_probability_pair M hM U _ _ _ _ hp hm hgeom.2.2,
    hgeom.1, hgeom.2.1, (rotation_coefficient_norm θ).1, (rotation_coefficient_norm θ).2]
  ring

end QAmpEst.Est.AEFresh
end


section

namespace QAmpEst.Est.AEFresh
open scoped Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem outcomeProb_mixture (M : ℕ) (hM : 0 < M) (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (χ : ι → Bool) (z0 : ι)
    (ha : 0 < succProb A χ z0) (ha1 : succProb A χ z0 < 1) (y : Fin M) :
    outcomeProb M A χ z0 y =
      (phaseProb M (theta (succProb A χ z0)/π) y +
        phaseProb M (-theta (succProb A χ z0)/π) y)/2 := by
  change normSum (fun z => estAmpState M A χ z0 (y,z)) = _
  rw [estAmpState_eq_circuitVec, normalized_initial A χ z0 ha ha1]
  rw [← (theta_facts ha.le ha1.le).2.2.1, ← (theta_facts ha.le ha1.le).2.2.2]
  have hg := normalized_geometry A hA χ z0 ha ha1
  have hr := normalized_rotation A hA χ z0 ha ha1
  exact circuit_rotation_marginal M hM _ _ _ _ hg.1 hg.2.1 hg.2.2 hr.1 hr.2 y

end QAmpEst.Est.AEFresh
end


section

namespace QAmpEst.Est.AEFresh
open scoped Real
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem eq_zero_of_normSum_zero (v : ι → ℂ) (hv : normSum v = 0) : v = 0 := by
  ext i
  apply Complex.normSq_eq_zero.mp
  apply le_antisymm
  · calc
      Complex.normSq (v i) ≤ normSum v :=
        Finset.single_le_sum (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
      _ = 0 := hv
  · exact Complex.normSq_nonneg _

theorem Qop_init_zero (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ)
    (χ : ι → Bool) (z0 : ι) (ha : succProb A χ z0 = 0) :
    (Qop A χ z0).mulVec (initState A z0) = initState A z0 := by
  have hg : goodPart χ (initState A z0) = 0 :=
    eq_zero_of_normSum_zero _ (by rw [normSum_good]; exact ha)
  have he : initState A z0 = badPart χ (initState A z0) := by
    have h := good_add_bad χ (initState A z0)
    rw [hg, zero_add] at h
    exact h.symm
  calc
    _ = (Qop A χ z0).mulVec (badPart χ (initState A z0)) := congrArg _ he
    _ = initState A z0 := by rw [Qop_bad A hA, ha, hg]; simpa using he.symm

theorem Qop_init_one (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ)
    (χ : ι → Bool) (z0 : ι) (ha : succProb A χ z0 = 1) :
    (Qop A χ z0).mulVec (initState A z0) = -initState A z0 := by
  have hb : badPart χ (initState A z0) = 0 :=
    eq_zero_of_normSum_zero _ (by rw [normSum_bad_init A hA, ha, sub_self])
  have he : initState A z0 = goodPart χ (initState A z0) := by
    have h := good_add_bad χ (initState A z0)
    rw [hb, add_zero] at h
    exact h.symm
  calc
    _ = (Qop A χ z0).mulVec (goodPart χ (initState A z0)) := congrArg _ he
    _ = -initState A z0 := by
      rw [Qop_good A hA, ha, hb]
      norm_num
      exact he.symm

theorem phaseExp_half : phaseExp (1/2) = -1 := by
  unfold phaseExp
  norm_num
  rw [show 2 * (π:ℂ) * Complex.I * (1/2:ℂ) = π * Complex.I by ring]
  exact Complex.exp_pi_mul_I

theorem outcomeProb_zero (M : ℕ) (hM : 0 < M) (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (χ : ι → Bool) (z0 : ι)
    (ha : succProb A χ z0 = 0) (y : Fin M) : outcomeProb M A χ z0 y = phaseProb M 0 y := by
  change normSum (fun z => estAmpState M A χ z0 (y,z)) = _
  rw [estAmpState_eq_circuitVec, circuit_probability_eigen M hM _ _ 0,
    normSum_init A hA, mul_one]
  rw [phaseExp_zero, one_smul]
  exact Qop_init_zero A hA χ z0 ha

theorem outcomeProb_one (M : ℕ) (hM : 0 < M) (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (χ : ι → Bool) (z0 : ι)
    (ha : succProb A χ z0 = 1) (y : Fin M) : outcomeProb M A χ z0 y = phaseProb M (1/2) y := by
  change normSum (fun z => estAmpState M A χ z0 (y,z)) = _
  rw [estAmpState_eq_circuitVec, circuit_probability_eigen M hM _ _ (1/2),
    normSum_init A hA, mul_one]
  rw [phaseExp_half, neg_one_smul]
  exact Qop_init_one A hA χ z0 ha

end QAmpEst.Est.AEFresh
end


section

noncomputable section
open scoped Real
namespace QAmpEst.Est.AEFresh

theorem phaseExp_nat_mul (t : ℝ) (j : ℕ) :
    phaseExp (t * j) = phaseExp t ^ j := by
  unfold phaseExp
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem phaseExp_eq_one_iff (t : ℝ) : phaseExp t = 1 ↔ ∃ z : ℤ, t = z := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := Complex.exp_eq_one_iff.mp h
    refine ⟨z, ?_⟩
    have hi := congrArg Complex.im hz
    simp [Complex.mul_re, Complex.mul_im] at hi
    nlinarith [Real.pi_pos]
  · rintro ⟨z, rfl⟩
    exact phaseExp_int z

theorem phaseExp_fin_difference_ne_one {M : ℕ} (hM : 0 < M)
    (x y : Fin M) (hxy : x ≠ y) :
    phaseExp (((x : ℕ) - (y : ℕ) : ℝ) / M) ≠ 1 := by
  intro h
  obtain ⟨z, hz⟩ := (phaseExp_eq_one_iff _).mp h
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hx : (x : ℝ) < M := by exact_mod_cast x.isLt
  have hy : (y : ℝ) < M := by exact_mod_cast y.isLt
  have hx0 : (0 : ℝ) ≤ (x : ℕ) := Nat.cast_nonneg _
  have hy0 : (0 : ℝ) ≤ (y : ℕ) := Nat.cast_nonneg _
  have he : ((x : ℕ) : ℝ) - (y : ℕ) = z * (M : ℝ) := (div_eq_iff hm.ne').mp hz
  have hzlo : (-1 : ℝ) < z := by nlinarith
  have hzhi : (z : ℝ) < 1 := by nlinarith
  have hz0 : z = 0 := by
    have : (-1 : ℤ) < z := by exact_mod_cast hzlo
    have : z < (1 : ℤ) := by exact_mod_cast hzhi
    omega
  subst z
  simp only [Int.cast_zero, zero_mul, sub_eq_zero] at he
  exact hxy (Fin.ext (by exact_mod_cast he))

theorem phaseExp_fin_difference_sum {M : ℕ} (hM : 0 < M) (x y : Fin M) :
    (∑ j : Fin M, phaseExp ((((x : ℕ) - (y : ℕ) : ℝ) / M) * (j : ℕ))) =
      if x = y then (M : ℂ) else 0 := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [phaseExp]
  · rw [if_neg hxy]
    simp_rw [phaseExp_nat_mul]
    rw [Fin.sum_univ_eq_sum_range]
    let z := phaseExp (((x : ℕ) - (y : ℕ) : ℝ) / M)
    have hn : z - 1 ≠ 0 := sub_ne_zero.mpr (phaseExp_fin_difference_ne_one hM x y hxy)
    have hp : z ^ M = 1 := by
      rw [← phaseExp_nat_mul]
      have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      rw [div_mul_cancel₀ _ hm]
      simpa only [Int.cast_sub, Int.cast_natCast] using
        phaseExp_int (((x : ℕ) : ℤ) - (y : ℕ))
    have hg := geom_sum_mul z M
    rw [hp, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_right hn

end QAmpEst.Est.AEFresh
end
end


section

noncomputable section
open scoped Real
namespace QAmpEst.Est.AEFresh

def phaseSeries (M : ℕ) (t : ℝ) : ℂ := ∑ j : Fin M, phaseExp (t * (j : ℕ))

theorem phaseSeries_geometric (M : ℕ) (t : ℝ) :
    phaseSeries M t * (phaseExp t - 1) = phaseExp (t * M) - 1 := by
  unfold phaseSeries
  simp_rw [phaseExp_nat_mul]
  rw [Fin.sum_univ_eq_sum_range]
  exact geom_sum_mul (phaseExp t) M

theorem phaseSeries_add_int (M : ℕ) (t : ℝ) (z : ℤ) :
    phaseSeries M (t + z) = phaseSeries M t := by
  unfold phaseSeries
  apply Finset.sum_congr rfl
  intro j _
  have he : (t + (z : ℝ)) * (j : ℕ) = t * (j : ℕ) + ((z * (j : ℕ) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [he, phaseExp_add_int]

theorem phaseExp_sub_one_normSq (t : ℝ) :
    Complex.normSq (phaseExp t - 1) = 4 * Real.sin (π * t) ^ 2 := by
  have he : phaseExp t = Complex.exp (Complex.I * ((2 * π * t : ℝ) : ℂ)) := by
    unfold phaseExp
    congr 1
    push_cast
    ring
  rw [he, Complex.normSq_eq_norm_sq, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * π * t / 2 = π * t by ring, Real.norm_eq_abs, sq_abs]
  ring

theorem phaseSeries_normSq (M : ℕ) (t : ℝ) (ht : phaseExp t ≠ 1) :
    Complex.normSq (phaseSeries M t) =
      Real.sin (π * (t * M)) ^ 2 / Real.sin (π * t) ^ 2 := by
  have he : phaseSeries M t = (phaseExp (t * M) - 1) / (phaseExp t - 1) :=
    (eq_div_iff (sub_ne_zero.mpr ht)).mpr (phaseSeries_geometric M t)
  rw [he, Complex.normSq_div, phaseExp_sub_one_normSq, phaseExp_sub_one_normSq]
  ring

theorem phaseProb_series (M : ℕ) (ω : ℝ) (y : Fin M) :
    phaseProb M ω y = Complex.normSq (phaseSeries M (ω - (y : ℕ) / M)) / (M : ℝ) ^ 2 := by
  rw [phaseProb_eq_normSq]
  unfold phaseAmplitude phaseSeries
  rw [Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_natCast]
  ring

theorem phaseProb_series_rep (M : ℕ) (ω : ℝ) (y : Fin M) :
    phaseProb M ω y =
      Complex.normSq (phaseSeries M (ω - (y : ℕ) / M - round (ω - (y : ℕ) / M))) / (M : ℝ) ^ 2 := by
  rw [phaseProb_series]
  have h := phaseSeries_add_int M (ω - (y : ℕ) / M - round (ω - (y : ℕ) / M))
    (round (ω - (y : ℕ) / M))
  rw [sub_add_cancel] at h
  rw [h]

end QAmpEst.Est.AEFresh
end
end


section

noncomputable section
namespace QAmpEst.Est.AEFresh

theorem phaseProb_add_int (M : ℕ) (ω : ℝ) (z : ℤ) (y : Fin M) :
    phaseProb M (ω + z) y = phaseProb M ω y := by
  rw [phaseProb_series, phaseProb_series]
  have he : ω + (z : ℝ) - (y : ℕ) / M = (ω - (y : ℕ) / M) + z := by ring
  rw [he, phaseSeries_add_int]

theorem phaseProb_grid {M : ℕ} (hM : 0 < M) (l y : Fin M) :
    phaseProb M (((l : ℕ) : ℝ) / M) y = if y = l then 1 else 0 := by
  rw [phaseProb_eq_normSq]
  have hm : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold phaseAmplitude
  have he : ((l : ℕ) : ℝ) / M - (y : ℕ) / M = ((l : ℕ) - (y : ℕ) : ℝ) / M := by ring
  rw [he, phaseExp_fin_difference_sum hM]
  by_cases h : y = l
  · subst y
    simp [hm]
  · simp [h, Ne.symm h]

end QAmpEst.Est.AEFresh
end
end


section

namespace QAmpEst.Est.AEFresh
open Matrix
open scoped ComplexConjugate

theorem normSum_mulVec_of_star_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (hB : star B * B = 1) (v : ι → ℂ) :
    normSum (B.mulVec v) = normSum v := by
  apply Complex.ofReal_injective
  rw [coe_normSum, coe_normSum]
  change dotProduct (star (B.mulVec v)) (B.mulVec v) = dotProduct (star v) v
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  change dotProduct (Matrix.vecMul (star v) (star B * B)) v = _
  rw [hB, Matrix.vecMul_one]

end QAmpEst.Est.AEFresh
end


section

noncomputable section
open scoped Real
namespace QAmpEst.Est.AEFresh

theorem fourier_entry (M : ℕ) (x y : Fin M) :
    ShorAlgorithms.Shared.fourierMatrix M x y =
      (Real.sqrt M : ℂ)⁻¹ * phaseExp (((x : ℕ) : ℝ) * (y : ℕ) / M) := by
  unfold ShorAlgorithms.Shared.fourierMatrix phaseExp
  congr 2
  push_cast
  ring

theorem fourier_star_mul (M : ℕ) (hM : 0 < M) :
    star (ShorAlgorithms.Shared.fourierMatrix M) * ShorAlgorithms.Shared.fourierMatrix M = 1 := by
  have hm : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hs : (Real.sqrt M : ℂ) * (Real.sqrt M : ℂ) = (M : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (Nat.cast_nonneg M)
  ext x y
  change (∑ j : Fin M, qftInv M x j * ShorAlgorithms.Shared.fourierMatrix M j y) = _
  have he : (∑ j : Fin M, qftInv M x j * ShorAlgorithms.Shared.fourierMatrix M j y) =
      (M : ℂ)⁻¹ * ∑ j : Fin M, phaseExp ((((y : ℕ) - (x : ℕ) : ℝ) / M) * (j : ℕ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [qftInv_entry, fourier_entry]
    have ha : -((x : ℕ) : ℝ) * (j : ℕ) / M + ((j : ℕ) : ℝ) * (y : ℕ) / M =
        (((y : ℕ) - (x : ℕ) : ℝ) / M) * (j : ℕ) := by ring
    rw [← ha, phaseExp_add, ← hs, mul_inv_rev]
    ring
  rw [he, phaseExp_fin_difference_sum hM]
  by_cases hxy : x = y
  · subst y
    simp [hm]
  · simp [hxy, Ne.symm hxy]

theorem qftInv_star_mul (M : ℕ) (hM : 0 < M) : star (qftInv M) * qftInv M = 1 := by
  have h := fourier_star_mul M hM
  have hh := mul_eq_one_comm.mp h
  simpa only [qftInv, star_star] using hh

theorem phaseExp_normSq (t : ℝ) : Complex.normSq (phaseExp t) = 1 := by
  apply Complex.ofReal_injective
  rw [Complex.normSq_eq_conj_mul_self]
  change star (phaseExp t) * phaseExp t = (1 : ℂ)
  rw [phaseExp_conj, ← phaseExp_add]
  simpa only [neg_add_cancel] using phaseExp_zero

theorem normSum_stateS (M : ℕ) (hM : 0 < M) (ω : ℝ) : normSum (stateS M ω) = 1 := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have he (j : Fin M) : stateS M ω j = phaseExp (ω * (j : ℕ)) / (Real.sqrt M : ℂ) := by
    unfold stateS phaseExp
    congr 1
    push_cast
    ring
  simp only [normSum, he, Complex.normSq_div, phaseExp_normSq, Complex.normSq_ofReal,
    Real.mul_self_sqrt (Nat.cast_nonneg M), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  exact mul_one_div_cancel hm

theorem phaseProb_sum (M : ℕ) (hM : 0 < M) (ω : ℝ) :
    ∑ y : Fin M, phaseProb M ω y = 1 := by
  change normSum ((qftInv M).mulVec (stateS M ω)) = 1
  rw [normSum_mulVec_of_star_mul _ (qftInv_star_mul M hM), normSum_stateS M hM]

theorem phaseProb_nonneg (M : ℕ) (ω : ℝ) (y : Fin M) : 0 ≤ phaseProb M ω y :=
  Complex.normSq_nonneg _

end QAmpEst.Est.AEFresh
end
end


section

namespace QAmpEst.Est.AEFresh
open scoped Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem outcomeProb_mixture_all (M : ℕ) (hM : 0 < M) (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (χ : ι → Bool) (z0 : ι) (y : Fin M) :
    outcomeProb M A χ z0 y =
      (phaseProb M (theta (succProb A χ z0)/π) y +
        phaseProb M (-theta (succProb A χ z0)/π) y)/2 := by
  have hab := succProb_bounds A hA χ z0
  by_cases ha : succProb A χ z0 = 0
  · rw [outcomeProb_zero M hM A hA χ z0 ha, ha]
    simp [theta]
  by_cases ha1 : succProb A χ z0 = 1
  · rw [outcomeProb_one M hM A hA χ z0 ha1, ha1]
    have ht : theta 1/π = (1/2:ℝ) := by simp [theta]; field_simp
    have htn : -theta 1/π = (-1/2:ℝ) := by rw [neg_div, ht]; ring
    have hp : phaseProb M (-1/2) y = phaseProb M (1/2) y := by
      have h := phaseProb_add_int M (-1/2) 1 y
      norm_num at h
      convert h.symm using 1
      norm_num
    rw [ht, htn, hp]
    ring
  exact outcomeProb_mixture M hM A hA χ z0 (lt_of_le_of_ne hab.1 (Ne.symm ha))
    (lt_of_le_of_ne hab.2 ha1) y

theorem outcomeProb_sum (M : ℕ) (hM : 0 < M) (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (χ : ι → Bool) (z0 : ι) :
    ∑ y : Fin M, outcomeProb M A χ z0 y = 1 := by
  simp_rw [outcomeProb_mixture_all M hM A hA χ z0]
  rw [← Finset.sum_div, Finset.sum_add_distrib, phaseProb_sum M hM, phaseProb_sum M hM]
  norm_num

theorem outcomeProb_nonneg (M : ℕ) (A : Matrix ι ι ℂ) (χ : ι → Bool)
    (z0 : ι) (y : Fin M) : 0 ≤ outcomeProb M A χ z0 y :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

end QAmpEst.Est.AEFresh
end


section

namespace QAmpEst.Est.AEFresh
open scoped Real

theorem sin_sq_add_identity (θ h : ℝ) :
    Real.sin (θ+h)^2 - Real.sin θ^2 =
      Real.sin (2*θ)*Real.sin h*Real.cos h + Real.cos (2*θ)*Real.sin h^2 := by
  rw [Real.sin_add, Real.sin_two_mul, Real.cos_two_mul]
  linear_combination (Real.sin θ)^2 * Real.sin_sq_add_cos_sq h -
    (Real.sin h)^2 * Real.sin_sq_add_cos_sq θ

theorem sin_sq_error (θ h : ℝ) :
    |Real.sin (θ+h)^2 - Real.sin θ^2| ≤ |Real.sin (2*θ)| *|h| + h^2 := by
  rw [sin_sq_add_identity]
  calc
    _ ≤ |Real.sin (2*θ)*Real.sin h*Real.cos h| +
        |Real.cos (2*θ)*Real.sin h^2| := abs_add_le _ _
    _ ≤ |Real.sin (2*θ)| *|h| + h^2 := by
      apply add_le_add
      · rw [abs_mul, abs_mul]
        calc
          _ ≤ (|Real.sin (2*θ)| *|h|)*1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (abs_nonneg _))
              (Real.abs_cos_le_one h) (abs_nonneg _) (by positivity)
          _ = _ := mul_one _
      · rw [abs_mul, abs_of_nonneg (sq_nonneg (Real.sin h))]
        calc
          _ ≤ 1*h^2 := mul_le_mul (Real.abs_cos_le_one (2*θ)) Real.sin_sq_le_sq
            (sq_nonneg _) zero_le_one
          _ = _ := one_mul _

theorem theta_error {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (h : ℝ) :
    |Real.sin (theta a+h)^2-a| ≤ 2*Real.sqrt (a*(1-a))*|h|+h^2 := by
  have he := sin_sq_error (theta a) h
  rw [theta_sin_sq ha ha1, double_theta_sin ha ha1,
    abs_of_nonneg (by positivity : 0 ≤ 2*Real.sqrt a*Real.sqrt (1-a))] at he
  rw [Real.sqrt_mul ha]
  nlinarith [he]

theorem neg_theta_error {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (h : ℝ) :
    |Real.sin (-theta a+h)^2-a| ≤ 2*Real.sqrt (a*(1-a))*|h|+h^2 := by
  have he := theta_error ha ha1 (-h)
  rw [abs_neg, neg_sq] at he
  have hh : Real.sin (-theta a+h)^2 = Real.sin (theta a+-h)^2 := by
    rw [show -theta a+h = -(theta a+-h) by ring, Real.sin_neg, neg_sq]
  rwa [hh]

end QAmpEst.Est.AEFresh
end


section

noncomputable section
namespace QAmpEst.Est.AEFresh

def circularRep (ω x : ℝ) : ℝ := x - ω - round (x - ω)

theorem circularRep_bounds (ω x : ℝ) :
    -(1 / 2 : ℝ) ≤ circularRep ω x ∧ circularRep ω x < 1 / 2 := by
  have h := (round_eq_iff (x := x - ω) (n := round (x - ω))).mp rfl
  dsimp [circularRep]
  constructor <;> linarith [h.1, h.2]

theorem circDist_eq_abs_rep (ω x : ℝ) : circDist ω x = |circularRep ω x| := by
  have hb : BddBelow (Set.range (fun z : ℤ => |(z : ℝ) + x - ω|)) :=
    ⟨0, by rintro _ ⟨z, rfl⟩; exact abs_nonneg _⟩
  apply le_antisymm
  · calc
      circDist ω x ≤ |((-(round (x - ω)) : ℤ) : ℝ) + x - ω| :=
        ciInf_le hb _
      _ = |circularRep ω x| := by congr 1; simp [circularRep]; ring
  · apply le_ciInf
    intro z
    have h := round_le (x - ω) (-z)
    simp only [Int.cast_neg] at h
    have he : x - ω - -(z : ℝ) = (z : ℝ) + x - ω := by ring
    rw [he] at h
    exact h

theorem circDist_nonneg (ω x : ℝ) : 0 ≤ circDist ω x := by
  rw [circDist_eq_abs_rep]
  exact abs_nonneg _

theorem circDist_le_half (ω x : ℝ) : circDist ω x ≤ 1 / 2 := by
  rw [circDist_eq_abs_rep]
  exact abs_le.mpr ⟨(circularRep_bounds ω x).1, (circularRep_bounds ω x).2.le⟩

theorem circularRep_add_int (ω x : ℝ) (z : ℤ) :
    circularRep ω (x + z) = circularRep ω x := by
  unfold circularRep
  rw [show x + (z : ℝ) - ω = x - ω + z by ring, round_add_intCast]
  push_cast
  ring

end QAmpEst.Est.AEFresh
end
end


section

namespace QAmpEst.Est.AEFresh

theorem circDist_le_integer (ω x : ℝ) (z : ℤ) :
    circDist ω x ≤ |(z : ℝ) + x - ω| := by
  apply ciInf_le
  exact ⟨0, by rintro _ ⟨j, rfl⟩; exact abs_nonneg _⟩

theorem circDist_symm (ω x : ℝ) : circDist ω x = circDist x ω := by
  have h (a b : ℝ) : circDist a b ≤ circDist b a := by
    rw [circDist_eq_abs_rep b a]
    calc
      circDist a b ≤ |(round (a - b) : ℝ) + b - a| := circDist_le_integer a b _
      _ = |circularRep b a| := by
        rw [show (round (a - b) : ℝ) + b - a = -circularRep b a by unfold circularRep; ring, abs_neg]
  exact le_antisymm (h ω x) (h x ω)

theorem circDist_add_right (ω x c : ℝ) : circDist (ω + c) (x + c) = circDist ω x := by
  unfold circDist
  congr 1
  funext z
  congr 1
  ring

theorem circDist_neg (ω x : ℝ) : circDist (-ω) (-x) = circDist ω x := by
  calc
    circDist (-ω) (-x) = circDist x ω := by
      have h := circDist_add_right (-ω) (-x) (ω + x)
      convert h.symm using 1
      congr 1 <;> ring
    _ = circDist ω x := circDist_symm x ω

theorem circDist_add_int_right (ω x : ℝ) (z : ℤ) :
    circDist ω (x + z) = circDist ω x := by
  rw [circDist_eq_abs_rep, circularRep_add_int, circDist_eq_abs_rep]

theorem circDist_add_int_left (ω x : ℝ) (z : ℤ) :
    circDist (ω + z) x = circDist ω x := by
  rw [circDist_symm, circDist_add_int_right, circDist_symm]

end QAmpEst.Est.AEFresh
end


section

namespace QAmpEst.Est.AEFresh
open scoped Real

theorem sin_sq_add_int_pi (x : ℝ) (n : ℤ) : Real.sin (x+n*π)^2 = Real.sin x^2 := by
  rw [Real.sin_sq_eq_half_sub, Real.sin_sq_eq_half_sub,
    show 2*(x+(n:ℝ)*π) = 2*x+(n:ℝ)*(2*π) by ring, Real.cos_add_int_mul_two_pi]

theorem estimate_eq_rep (M : ℕ) (y : Fin M) (θ : ℝ) :
    estimate M y = Real.sin (θ+π*circularRep (θ/π) ((y:ℕ)/M))^2 := by
  have he : θ+π*circularRep (θ/π) ((y:ℕ)/M) =
      π*(y:ℕ)/M + (-(round (((y:ℕ):ℝ)/M-θ/π)) : ℤ)*π := by
    unfold circularRep
    push_cast
    field_simp
    ring
  rw [he, sin_sq_add_int_pi]
  rfl

theorem estimate_transfer (M : ℕ) (hM : 0 < M) (k : ℕ) (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (θ : ℝ) (hθ : θ = theta a ∨ θ = -theta a)
    (y : Fin M) (hy : circDist (((y:ℕ):ℝ)/M) (θ/π) ≤ (k:ℝ)/M) :
    |estimate M y-a| ≤ 2*π*(k:ℝ)*Real.sqrt (a*(1-a))/(M:ℝ) +
      (k:ℝ)^2*π^2/(M:ℝ)^2 := by
  let h : ℝ := π*circularRep (θ/π) (((y:ℕ):ℝ)/M)
  let R : ℝ := π*(k:ℝ)/(M:ℝ)
  have hMpos : (0:ℝ) < M := by exact_mod_cast hM
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hbound : |h| ≤ R := by
    rw [circDist_symm, circDist_eq_abs_rep] at hy
    dsimp [h, R]
    rw [abs_mul, abs_of_pos Real.pi_pos]
    simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hy Real.pi_pos.le
  have herr : |Real.sin (θ+h)^2-a| ≤ 2*Real.sqrt (a*(1-a))*|h|+h^2 := by
    rcases hθ with rfl | rfl
    · exact theta_error ha ha1 h
    · exact neg_theta_error ha ha1 h
  rw [estimate_eq_rep M y θ]
  change |Real.sin (θ+h)^2-a| ≤ _
  calc
    _ ≤ 2*Real.sqrt (a*(1-a))*|h|+h^2 := herr
    _ ≤ 2*Real.sqrt (a*(1-a))*R+R^2 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hbound (by positivity)
      · exact sq_le_sq.mpr (by simpa [abs_of_nonneg hR] using hbound)
    _ = _ := by dsimp [R]; ring

theorem estimate_bounds (M : ℕ) (y : Fin M) : 0 ≤ estimate M y ∧ estimate M y ≤ 1 := by
  exact ⟨sq_nonneg _, by simpa [estimate] using Real.sin_sq_le_one (π*(y:ℕ)/M)⟩

end QAmpEst.Est.AEFresh
end


section

namespace QAmpEst.Est.AEFresh
open scoped Real
noncomputable section

def errorThreshold (a : ℝ) (M k : ℕ) : ℝ :=
  2*π*(k:ℝ)*Real.sqrt (a*(1-a))/(M:ℝ)+(k:ℝ)^2*π^2/(M:ℝ)^2

def estimateEvent (a : ℝ) (M k : ℕ) : Finset (Fin M) :=
  Finset.univ.filter (fun y => |estimate M y-a| ≤ errorThreshold a M k)

def phaseEvent (ω : ℝ) (M k : ℕ) : Finset (Fin M) :=
  Finset.univ.filter (fun y => circDist (((y:ℕ):ℝ)/M) ω ≤ (k:ℝ)/M)

theorem phaseEvent_subset_estimateEvent (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (M : ℕ) (hM : 0 < M) (k : ℕ) (θ : ℝ) (hθ : θ=theta a ∨ θ=-theta a) :
    phaseEvent (θ/π) M k ⊆ estimateEvent a M k := by
  intro y hy
  simp only [phaseEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  simp only [estimateEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact estimate_transfer M hM k a ha ha1 θ hθ y hy

theorem phase_mass_transfer (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (M : ℕ) (hM : 0 < M) (k : ℕ) (θ : ℝ) (hθ : θ=theta a ∨ θ=-theta a)
    (P : Fin M → ℝ) (hP : ∀y,0≤P y) :
    ∑y∈phaseEvent (θ/π) M k,P y ≤ ∑y∈estimateEvent a M k,P y := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (phaseEvent_subset_estimateEvent a ha ha1 M hM k θ hθ) (fun i _ _ => hP i)

theorem small_M_event_univ (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (M : ℕ) (hM : 0 < M) (hM2 : M ≤ 2) (k : ℕ) (hk : 1 ≤ k) :
    estimateEvent a M k = Finset.univ := by
  unfold estimateEvent
  apply Finset.filter_eq_self.mpr
  intro y _
  have hy := estimate_bounds M y
  have hdiff : |estimate M y-a| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hMp : (0:ℝ)<M := by exact_mod_cast hM
  have hMle : (M:ℝ)≤2 := by exact_mod_cast hM2
  have hkle : (1:ℝ)≤k := by exact_mod_cast hk
  have hterm : 1 ≤ (k:ℝ)^2*π^2/(M:ℝ)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hMp)).mpr
    nlinarith [Real.pi_gt_three, sq_nonneg ((k:ℝ)-1)]
  have hnon : 0 ≤ 2*π*(k:ℝ)*Real.sqrt (a*(1-a))/(M:ℝ) := by positivity
  dsimp only [errorThreshold]
  linarith

end
end QAmpEst.Est.AEFresh
end


section

noncomputable section
open scoped Real
namespace QAmpEst.Est.AEFresh

theorem phaseExp_ne_one_of_small {t : ℝ} (ht : t ≠ 0) (hb : |t| ≤ 1 / 2) :
    phaseExp t ≠ 1 := by
  intro h
  obtain ⟨z, rfl⟩ := (phaseExp_eq_one_iff t).mp h
  have hzlo : (-1 : ℤ) < z := by
    have : (-1 : ℝ) < z := by linarith [(abs_le.mp hb).1]
    exact_mod_cast this
  have hzhi : z < (1 : ℤ) := by
    have : (z : ℝ) < 1 := by linarith [(abs_le.mp hb).2]
    exact_mod_cast this
  have : z = 0 := by omega
  exact ht (by simp [this])

theorem sine_denominator_lower {t : ℝ} (hb : |t| ≤ 1 / 2) :
    4 * t ^ 2 ≤ Real.sin (π * t) ^ 2 := by
  have hx : |π * t| ≤ π / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have h := Real.mul_abs_le_abs_sin hx
  rw [abs_mul, abs_of_pos Real.pi_pos] at h
  have he : 2 / π * (π * |t|) = 2 * |t| := by field_simp
  rw [he] at h
  have hh := pow_le_pow_left₀ (show 0 ≤ 2 * |t| by positivity) h 2
  norm_num [mul_pow, sq_abs] at hh
  exact hh

theorem phaseSeries_pointwise (M : ℕ) {t : ℝ} (ht : t ≠ 0) (hb : |t| ≤ 1 / 2) :
    Complex.normSq (phaseSeries M t) ≤ 1 / (4 * t ^ 2) := by
  rw [phaseSeries_normSq M t (phaseExp_ne_one_of_small ht hb)]
  have hs := sine_denominator_lower hb
  have ht0 : 0 < 4 * t ^ 2 := by positivity
  have hs0 : 0 < Real.sin (π * t) ^ 2 := lt_of_lt_of_le ht0 hs
  apply (div_le_div_iff₀ hs0 ht0).mpr
  have hn := Real.sin_sq_le_one (π * (t * M))
  nlinarith [mul_nonneg (sub_nonneg.mpr hn) ht0.le]

theorem phaseProb_pointwise {M : ℕ} (hM : 0 < M) (ω : ℝ) (y : Fin M)
    (hd : 0 < circDist ω ((y : ℕ) / M)) :
    phaseProb M ω y ≤ 1 / (4 * (M : ℝ) ^ 2 * circDist ω ((y : ℕ) / M) ^ 2) := by
  let t := circularRep (((y : ℕ) : ℝ) / M) ω
  have he : circDist ω ((y : ℕ) / M) = |t| := by
    rw [circDist_symm, circDist_eq_abs_rep]
  have hb : |t| ≤ 1 / 2 := by
    rw [← he]
    exact circDist_le_half _ _
  have ht : t ≠ 0 := by intro h; simp [he, h] at hd
  have hm : 0 < (M : ℝ) ^ 2 := by positivity
  have hs := div_le_div_of_nonneg_right (phaseSeries_pointwise M ht hb) hm.le
  rw [phaseProb_series_rep]
  change Complex.normSq (phaseSeries M t) / (M : ℝ) ^ 2 ≤ _
  rw [he, sq_abs]
  calc
    Complex.normSq (phaseSeries M t) / (M : ℝ) ^ 2 ≤ (1 / (4 * t ^ 2)) / (M : ℝ) ^ 2 := hs
    _ = _ := by ring

end QAmpEst.Est.AEFresh
end
end


section

noncomputable section
namespace QAmpEst.Est.AEFresh

def phaseGridIndex (M : ℕ) (ω : ℝ) (y : Fin M) : ℤ :=
  (y : ℕ) - (M : ℤ) * round (((y : ℕ) : ℝ) / M - ω)

theorem phaseGridIndex_injective (M : ℕ) (ω : ℝ) :
    Function.Injective (phaseGridIndex M ω) := by
  intro x y h
  have hm := congrArg (fun z : ℤ => z % (M : ℤ)) h
  simp only [phaseGridIndex, Int.sub_mul_emod_self_left] at hm
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast x.isLt),
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast y.isLt)] at hm
  exact Fin.ext (by exact_mod_cast hm)

theorem phaseGridIndex_rep {M : ℕ} (hM : 0 < M) (ω : ℝ) (y : Fin M) :
    (phaseGridIndex M ω y : ℝ) - M * ω =
      M * circularRep ω (((y : ℕ) : ℝ) / M) := by
  unfold phaseGridIndex circularRep
  push_cast
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp
  ring

def signedShell (r : ℝ) : Bool × ℤ := (decide (0 ≤ r), ⌊|r|⌋)

theorem signedShell_integer_injective (c : ℝ) :
    Function.Injective (fun z : ℤ => signedShell ((z : ℝ) - c)) := by
  intro z w h
  have hsg := congrArg Prod.fst h
  have hfl := congrArg Prod.snd h
  change decide (0 ≤ (z : ℝ) - c) = decide (0 ≤ (w : ℝ) - c) at hsg
  change ⌊|(z : ℝ) - c|⌋ = ⌊|(w : ℝ) - c|⌋ at hfl
  have hs : (0 ≤ (z : ℝ) - c) ↔ (0 ≤ (w : ℝ) - c) := by simpa using hsg
  by_cases hz : 0 ≤ (z : ℝ) - c
  · rw [abs_of_nonneg hz, abs_of_nonneg (hs.mp hz)] at hfl
    simp only [sub_eq_add_neg, Int.floor_intCast_add] at hfl
    omega
  · have hw : (w : ℝ) - c < 0 := lt_of_not_ge (fun h => hz (hs.mpr h))
    rw [abs_of_neg (lt_of_not_ge hz), abs_of_neg hw] at hfl
    have he (v : ℤ) : -((v : ℝ) - c) = ((-v : ℤ) : ℝ) + c := by push_cast; ring
    simp only [he, Int.floor_intCast_add] at hfl
    omega

theorem phase_shell_injective (M : ℕ) (ω : ℝ) :
    Function.Injective (fun y : Fin M => signedShell ((phaseGridIndex M ω y : ℝ) - M * ω)) :=
  (signedShell_integer_injective ((M : ℝ) * ω)).comp (phaseGridIndex_injective M ω)

theorem bad_shell_lower (r : ℝ) (k : ℕ) (h : (k : ℝ) < |r|) :
    (k : ℤ) ≤ (signedShell r).2 := by
  exact Int.le_floor.mpr (by exact_mod_cast h.le)

end QAmpEst.Est.AEFresh
end
end


section

namespace QAmpEst.Est.AEFresh

theorem reciprocal_square_le_telescope {x : ℝ} (hx : 1 < x) :
    1 / x ^ 2 ≤ 1 / (x - 1) - 1 / x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  field_simp
  nlinarith

theorem finite_reciprocal_tail (k N : ℕ) (hk : 2 ≤ k) :
    (∑ i ∈ Finset.range N, 1 / ((k + i : ℕ) : ℝ) ^ 2) ≤
      1 / ((k : ℝ) - 1) - 1 / ((k + N : ℕ) - 1 : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hx : 1 < ((k + N : ℕ) : ℝ) := by exact_mod_cast (show 1 < k + N by omega)
    have h := reciprocal_square_le_telescope hx
    have he : (((k + (N + 1) : ℕ) : ℝ) - 1) = (k + N : ℕ) := by push_cast; ring
    rw [he]
    linarith

theorem finite_reciprocal_tail_strict (k N : ℕ) (hk : 2 ≤ k) :
    (∑ i ∈ Finset.range N, 1 / ((k + i : ℕ) : ℝ) ^ 2) <
      1 / ((k : ℝ) - 1) := by
  have h := finite_reciprocal_tail k N hk
  have hp : 0 < 1 / ((k + N : ℕ) - 1 : ℝ) := by
    apply one_div_pos.mpr
    have : (1 : ℝ) < (k + N : ℕ) := by exact_mod_cast (show 1 < k + N by omega)
    linarith
  linarith

end QAmpEst.Est.AEFresh
end


section

namespace QAmpEst.Est.AEFresh

theorem finite_shell_tail {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (key : ι → Bool × ℕ) (p : ι → ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hinj : Set.InjOn key (s : Set ι))
    (hlower : ∀ i ∈ s, k ≤ (key i).2)
    (hbound : ∀ i ∈ s, p i ≤ 1 / (4 * ((key i).2 : ℝ) ^ 2)) :
    ∑ i ∈ s, p i < 1 / (2 * ((k : ℝ) - 1)) := by
  classical
  let N := s.sup (fun i => (key i).2) + 1
  let f : ι → Bool × ℕ := fun i => ((key i).1, (key i).2 - k)
  let w : Bool × ℕ → ℝ := fun q => 1 / (4 * ((k + q.2 : ℕ) : ℝ) ^ 2)
  have hf : Set.InjOn f (s : Set ι) := by
    intro i hi j hj hij
    apply hinj hi hj
    apply Prod.ext
    · simpa only [f] using congrArg Prod.fst hij
    · have h := congrArg Prod.snd hij
      dsimp [f] at h
      have hi' := hlower i hi
      have hj' := hlower j hj
      omega
  have hs : s.image f ⊆ (Finset.univ : Finset Bool) ×ˢ Finset.range N := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_range]
    have h := Finset.le_sup (f := fun i => (key i).2) hi
    dsimp [f, N]
    omega
  have hsum : ∑ i ∈ s, p i ≤
      (1 / 2 : ℝ) * ∑ j ∈ Finset.range N, 1 / ((k + j : ℕ) : ℝ) ^ 2 := by
    calc
      ∑ i ∈ s, p i ≤ ∑ i ∈ s, w (f i) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [w, f, Nat.add_sub_of_le (hlower i hi)] using hbound i hi
      _ = ∑ q ∈ s.image f, w q := (Finset.sum_image hf).symm
      _ ≤ ∑ q ∈ (Finset.univ : Finset Bool) ×ˢ Finset.range N, w q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hs
        intro q _ _
        dsimp [w]
        positivity
      _ = _ := by
        simp only [Finset.sum_product, Fintype.sum_bool, w]
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have ht := finite_reciprocal_tail_strict k N hk
  have hh : (1 / 2 : ℝ) * (∑ j ∈ Finset.range N, 1 / ((k + j : ℕ) : ℝ) ^ 2) <
      (1 / 2 : ℝ) * (1 / ((k : ℝ) - 1)) := by linarith
  have he : (1 / 2 : ℝ) * (1 / ((k : ℝ) - 1)) = 1 / (2 * ((k : ℝ) - 1)) := by simp only [one_div, mul_inv_rev]; ring
  rw [he] at hh
  exact hsum.trans_lt hh

end QAmpEst.Est.AEFresh
end


section

noncomputable section
namespace QAmpEst.Est.AEFresh

theorem phase_bad_mass_strict {M : ℕ} (hM : 0 < M) (ω : ℝ) (k : ℕ) (hk : 2 ≤ k) :
    (∑ y ∈ Finset.univ.filter (fun y : Fin M => (k : ℝ) / M < circDist ω ((y : ℕ) / M)),
      phaseProb M ω y) < 1 / (2 * ((k : ℝ) - 1)) := by
  classical
  let r : Fin M → ℝ := fun y => (phaseGridIndex M ω y : ℝ) - M * ω
  let key : Fin M → Bool × ℕ := fun y => ((signedShell (r y)).1, (signedShell (r y)).2.toNat)
  have hr (y : Fin M) : |r y| = (M : ℝ) * circDist ω ((y : ℕ) / M) := by
    dsimp [r]
    rw [phaseGridIndex_rep hM, abs_mul, abs_of_pos (by exact_mod_cast hM), circDist_eq_abs_rep]
  have hj (y : Fin M) : 0 ≤ (signedShell (r y)).2 := Int.floor_nonneg.mpr (abs_nonneg _)
  have hkey : Function.Injective key := by
    intro x y h
    apply phase_shell_injective M ω
    apply Prod.ext
    · simpa only [key, r] using congrArg Prod.fst h
    · have hh := congrArg Prod.snd h
      change ((signedShell (r x)).2).toNat = ((signedShell (r y)).2).toNat at hh
      have hxj := hj x
      have hyj := hj y
      change (signedShell (r x)).2 = (signedShell (r y)).2
      omega
  apply finite_shell_tail _ key (phaseProb M ω) k hk hkey.injOn
  · intro y hy
    have hb := (Finset.mem_filter.mp hy).2
    have hm : (0 : ℝ) < M := by exact_mod_cast hM
    have hkr : (k : ℝ) < |r y| := by rw [hr]; simpa only [mul_comm] using (div_lt_iff₀ hm).mp hb
    have hh := bad_shell_lower (r y) k hkr
    change k ≤ ((signedShell (r y)).2).toNat
    exact_mod_cast (show (k : ℤ) ≤ ↑((signedShell (r y)).2).toNat by simpa only [Int.toNat_of_nonneg (hj y)] using hh)
  · intro y hy
    have hb := (Finset.mem_filter.mp hy).2
    have hm : (0 : ℝ) < M := by exact_mod_cast hM
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hd : 0 < circDist ω ((y : ℕ) / M) := (div_pos hk0 hm).trans hb
    have hp := phaseProb_pointwise hM ω y hd
    have hfloor : ((key y).2 : ℝ) ≤ |r y| := by
      dsimp [key, signedShell]
      have hc : (((⌊|r y|⌋ : ℤ).toNat : ℕ) : ℝ) = (⌊|r y|⌋ : ℤ) := by
        exact_mod_cast Int.toNat_of_nonneg (Int.floor_nonneg.mpr (abs_nonneg (r y)))
      rw [hc]
      exact Int.floor_le _
    have hkn : (k : ℤ) ≤ (signedShell (r y)).2 := by
      apply bad_shell_lower
      rw [hr]
      simpa only [mul_comm] using (div_lt_iff₀ hm).mp hb
    have hkp : (0 : ℝ) < (key y).2 := by
      have : (0 : ℤ) < (signedShell (r y)).2 := lt_of_lt_of_le (by exact_mod_cast (show 0 < k by omega)) hkn
      have : 0 < ((signedShell (r y)).2).toNat := by omega
      exact_mod_cast this
    have hsq : ((key y).2 : ℝ) ^ 2 ≤ |r y| ^ 2 := pow_le_pow_left₀ hkp.le hfloor 2
    calc
      phaseProb M ω y ≤ 1 / (4 * |r y| ^ 2) := by simpa only [hr, mul_pow, mul_assoc] using hp
      _ ≤ 1 / (4 * ((key y).2 : ℝ) ^ 2) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith)

theorem phase_good_mass_strict {M : ℕ} (hM : 0 < M) (ω : ℝ) (k : ℕ) (hk : 2 ≤ k) :
    1 - 1 / (2 * ((k : ℝ) - 1)) <
      ∑ y ∈ Finset.univ.filter (fun y : Fin M => circDist ω ((y : ℕ) / M) ≤ (k : ℝ) / M),
        phaseProb M ω y := by
  classical
  have ht := phase_bad_mass_strict hM ω k hk
  have hs := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (fun y : Fin M => circDist ω ((y : ℕ) / M) ≤ (k : ℝ) / M) (phaseProb M ω)
  simp only [not_le, phaseProb_sum M hM ω] at hs
  linarith

end QAmpEst.Est.AEFresh
end
end


section

noncomputable section
namespace QAmpEst.Est.AEFresh

def residueGrid (M : ℕ) (hM : 0 < M) (z : ℤ) : Fin M :=
  ⟨(z % (M : ℤ)).toNat, by
    have hn : 0 ≤ z % (M : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hM.ne')
    have hl : z % (M : ℤ) < M := Int.emod_lt_of_pos _ (by exact_mod_cast hM)
    exact (Int.toNat_lt hn).mpr hl⟩

theorem residueGrid_cast (M : ℕ) (hM : 0 < M) (z : ℤ) :
    ((residueGrid M hM z : ℕ) : ℤ) = z % (M : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hM.ne'))

theorem residueGrid_decompose (M : ℕ) (hM : 0 < M) (z : ℤ) :
    (z : ℝ) / M = ((residueGrid M hM z : ℕ) : ℝ) / M + ((z / (M : ℤ) : ℤ) : ℝ) := by
  have he := Int.emod_add_ediv_mul z (M : ℤ)
  have hr : ((residueGrid M hM z : ℕ) : ℝ) + ((z / (M : ℤ) : ℤ) : ℝ) * M = z := by
    rw [← Int.cast_natCast, residueGrid_cast]
    exact_mod_cast he
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  apply (div_eq_iff hm).mpr
  field_simp
  linarith

theorem residueGrid_consecutive_ne (M : ℕ) (hM : 1 < M) (z : ℤ) :
    residueGrid M (by omega) z ≠ residueGrid M (by omega) (z + 1) := by
  intro h
  have he := congrArg (fun y : Fin M => ((y : ℕ) : ℤ)) h
  rw [residueGrid_cast, residueGrid_cast] at he
  have h0 := Int.emod_add_ediv_mul z (M : ℤ)
  have h1 := Int.emod_add_ediv_mul (z + 1) (M : ℤ)
  have hd : (M : ℤ) ∣ 1 := by
    refine ⟨(z + 1) / (M : ℤ) - z / (M : ℤ), ?_⟩
    nlinarith
  have hm : (1 : ℤ) < M := by exact_mod_cast hM
  have ha := Int.le_of_dvd (by norm_num : (0 : ℤ) < 1) hd
  omega

theorem phaseProb_residue_offset (M : ℕ) (hM : 0 < M) (z : ℤ) (t : ℝ) :
    phaseProb M (((z : ℝ) + t) / M) (residueGrid M hM z) =
      Complex.normSq (phaseSeries M (t / M)) / (M : ℝ) ^ 2 := by
  have he : ((z : ℝ) + t) / M =
      (((residueGrid M hM z : ℕ) : ℝ) / M + t / M) + ((z / (M : ℤ) : ℤ) : ℝ) := by
    rw [add_div, residueGrid_decompose M hM z]
    ring
  rw [he, phaseProb_add_int, phaseProb_series]
  have hh : ((residueGrid M hM z : ℕ) : ℝ) / M + t / M -
      (residueGrid M hM z : ℕ) / M = t / M := by ring
  rw [hh]

theorem residue_distance_le (M : ℕ) (hM : 0 < M) (z : ℤ) (t : ℝ) :
    circDist (((z : ℝ) + t) / M) (((residueGrid M hM z : ℕ) : ℝ) / M) ≤ |t| / M := by
  have he := residueGrid_decompose M hM z
  calc
    circDist (((z : ℝ) + t) / M) (((residueGrid M hM z : ℕ) : ℝ) / M) ≤
        |((z / (M : ℤ) : ℤ) : ℝ) + ((residueGrid M hM z : ℕ) : ℝ) / M - ((z : ℝ) + t) / M| :=
      circDist_le_integer _ _ _
    _ = |t| / M := by
      rw [add_div]
      rw [he]
      have hh : ((z / (M : ℤ) : ℤ) : ℝ) + ((residueGrid M hM z : ℕ) : ℝ) / M -
          (((residueGrid M hM z : ℕ) : ℝ) / M + ((z / (M : ℤ) : ℤ) : ℝ) + t / M) = -(t / M) := by ring
      rw [hh, abs_neg, abs_div, abs_of_pos (show (0 : ℝ) < M by exact_mod_cast hM)]

end QAmpEst.Est.AEFresh
end
end


section

open scoped Real
namespace QAmpEst.Est.AEFresh

theorem sine_quarter_chord {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) :
    2 * Real.sqrt 2 * t ≤ Real.sin (π * t) := by
  have h : (1 - 4 * t) • Real.sin 0 + (4 * t) • Real.sin (π / 4) ≤
      Real.sin ((1 - 4 * t) • (0 : ℝ) + (4 * t) • (π / 4)) :=
    strictConcaveOn_sin_Icc.concaveOn.2
      (show (0 : ℝ) ∈ Set.Icc 0 π by constructor <;> linarith [Real.pi_pos])
      (show π / 4 ∈ Set.Icc 0 π by constructor <;> linarith [Real.pi_pos])
      (by linarith) (by linarith) (by ring)
  simp only [smul_eq_mul, Real.sin_zero, mul_zero, zero_add, Real.sin_pi_div_four] at h
  convert h using 1 <;> ring

theorem sine_middle_lower {t : ℝ} :
    1 - 5 * (1 / 2 - t) ^ 2 ≤ Real.sin (π * t) := by
  have h := Real.one_sub_sq_div_two_le_cos (x := π * (1 / 2 - t))
  have hp : π ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hs : Real.cos (π * (1 / 2 - t)) = Real.sin (π * t) := by
    rw [show π * (1 / 2 - t) = π / 2 - π * t by ring, Real.cos_pi_div_two_sub]
  rw [hs] at h
  nlinarith [sq_nonneg (1 / 2 - t), mul_nonneg (le_of_lt (sub_pos.mpr hp)) (sq_nonneg (1 / 2 - t))]

theorem nearest_two_scalar_half {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    8 ≤ Real.sin (π * t) ^ 2 * (1 / t ^ 2 + 1 / (1 - t) ^ 2) := by
  have ht1 : 0 < 1 - t := by linarith
  by_cases hq : t ≤ 1 / 4
  · have hs := sine_quarter_chord ht.le hq
    have hsq : 8 * t ^ 2 ≤ Real.sin (π * t) ^ 2 := by
      have hh := pow_le_pow_left₀ (show 0 ≤ 2 * Real.sqrt 2 * t by positivity) hs 2
      norm_num [mul_pow, Real.sq_sqrt] at hh
      linarith
    have hfirst : 8 ≤ Real.sin (π * t) ^ 2 / t ^ 2 := (le_div_iff₀ (sq_pos_of_pos ht)).mpr hsq
    have hsecond : 0 ≤ Real.sin (π * t) ^ 2 / (1 - t) ^ 2 := by positivity
    calc
      8 ≤ Real.sin (π * t) ^ 2 / t ^ 2 + Real.sin (π * t) ^ 2 / (1 - t) ^ 2 := by linarith
      _ = _ := by ring
  · let v := (1 / 2 - t) ^ 2
    have hv : 0 ≤ v := sq_nonneg _
    have hv' : v ≤ 1 / 16 := by dsimp [v]; nlinarith
    have hs := sine_middle_lower (t := t)
    have hl : 0 ≤ 1 - 5 * v := by linarith
    have hsq : (1 - 5 * v) ^ 2 ≤ Real.sin (π * t) ^ 2 := by
      exact pow_le_pow_left₀ hl hs 2
    have hpoly : 0 ≤ v * (1 - 31 / 2 * v + 50 * v ^ 2) := by
      apply mul_nonneg hv
      nlinarith [sq_nonneg v]
    have hid : (1 - 5 * v) ^ 2 * (t ^ 2 + (1 - t) ^ 2) -
        8 * (t ^ 2 * (1 - t) ^ 2) = v * (1 - 31 / 2 * v + 50 * v ^ 2) := by
      dsimp [v]
      ring
    have hmul := mul_nonneg (sub_nonneg.mpr hsq)
      (show 0 ≤ t ^ 2 + (1 - t) ^ 2 by positivity)
    have hmain : 8 * (t ^ 2 * (1 - t) ^ 2) ≤
        Real.sin (π * t) ^ 2 * (t ^ 2 + (1 - t) ^ 2) := by nlinarith
    have he : Real.sin (π * t) ^ 2 * (1 / t ^ 2 + 1 / (1 - t) ^ 2) =
        (Real.sin (π * t) ^ 2 * (t ^ 2 + (1 - t) ^ 2)) / (t ^ 2 * (1 - t) ^ 2) := by
      field_simp
      ring
    rw [he]
    exact (le_div_iff₀ (by positivity)).mpr hmain

theorem nearest_two_scalar {t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    8 ≤ Real.sin (π * t) ^ 2 * (1 / t ^ 2 + 1 / (1 - t) ^ 2) := by
  by_cases hh : t ≤ 1 / 2
  · exact nearest_two_scalar_half ht hh
  · have h := nearest_two_scalar_half (t := 1 - t) (by linarith) (by linarith)
    have hs : Real.sin (π * (1 - t)) = Real.sin (π * t) := by
      rw [show π * (1 - t) = π - π * t by ring, Real.sin_pi_sub]
    simpa only [hs, sub_sub_cancel, add_comm] using h

end QAmpEst.Est.AEFresh
end


section

noncomputable section
open scoped Real
namespace QAmpEst.Est.AEFresh

theorem phaseProb_residue_lower (M : ℕ) (hM : 2 < M) (z : ℤ) (t : ℝ)
    (ht : t ≠ 0) (ht1 : |t| < 1) :
    Real.sin (π * t) ^ 2 / (π ^ 2 * t ^ 2) ≤
      phaseProb M (((z : ℝ) + t) / M) (residueGrid M (by omega) z) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hb : |t / M| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hm]
    apply (div_le_iff₀ hm).mpr
    have : (2 : ℝ) < M := by exact_mod_cast hM
    linarith
  have htn : t / (M : ℝ) ≠ 0 := div_ne_zero ht hm.ne'
  have hs := sine_denominator_lower hb
  have hsp : 0 < Real.sin (π * (t / M)) ^ 2 := by
    have : 0 < 4 * (t / (M : ℝ)) ^ 2 := by positivity
    linarith
  have hden : (M : ℝ) ^ 2 * Real.sin (π * (t / M)) ^ 2 ≤ π ^ 2 * t ^ 2 := by
    have h := Real.sin_sq_le_sq (x := π * (t / M))
    have hh := mul_le_mul_of_nonneg_left h (sq_nonneg (M : ℝ))
    have he : (M : ℝ) ^ 2 * (π * (t / M)) ^ 2 = π ^ 2 * t ^ 2 := by field_simp
    rwa [he] at hh
  rw [phaseProb_residue_offset, phaseSeries_normSq M (t / M) (phaseExp_ne_one_of_small htn hb)]
  rw [div_mul_cancel₀ _ hm.ne']
  have he : (Real.sin (π * t) ^ 2 / Real.sin (π * (t / M)) ^ 2) / (M : ℝ) ^ 2 =
      Real.sin (π * t) ^ 2 / ((M : ℝ) ^ 2 * Real.sin (π * (t / M)) ^ 2) := by ring
  rw [he]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden

theorem nearest_pair_probability (M : ℕ) (hM : 2 < M) (z : ℤ) (t : ℝ)
    (ht : 0 < t) (ht1 : t < 1) :
    8 / π ^ 2 ≤
      phaseProb M (((z : ℝ) + t) / M) (residueGrid M (by omega) z) +
      phaseProb M (((z : ℝ) + t) / M) (residueGrid M (by omega) (z + 1)) := by
  have h0 := phaseProb_residue_lower M hM z t ht.ne' (by rwa [abs_of_pos ht])
  have h1 := phaseProb_residue_lower M hM (z + 1) (t - 1) (by linarith) (by rw [abs_of_neg (by linarith)]; linarith)
  have he : (((z + 1 : ℤ) : ℝ) + (t - 1)) / M = ((z : ℝ) + t) / M := by push_cast; ring
  rw [he] at h1
  have hs : Real.sin (π * (t - 1)) ^ 2 = Real.sin (π * t) ^ 2 := by
    rw [show π * (t - 1) = π * t - π by ring, Real.sin_sub_pi, neg_sq]
  rw [hs, show (t - 1) ^ 2 = (1 - t) ^ 2 by ring] at h1
  have hb := nearest_two_scalar ht ht1
  have hp : 0 < π ^ 2 := sq_pos_of_pos Real.pi_pos
  have hh := div_le_div_of_nonneg_right hb hp.le
  have hid : (Real.sin (π * t) ^ 2 * (1 / t ^ 2 + 1 / (1 - t) ^ 2)) / π ^ 2 =
      Real.sin (π * t) ^ 2 / (π ^ 2 * t ^ 2) +
      Real.sin (π * t) ^ 2 / (π ^ 2 * (1 - t) ^ 2) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hid] at hh
  linarith

end QAmpEst.Est.AEFresh
end
end


section

noncomputable section
open scoped Real
namespace QAmpEst.Est.AEFresh

theorem phaseProb_integer_grid {M : ℕ} (hM : 0 < M) (z : ℤ) :
    phaseProb M ((z : ℝ) / M) (residueGrid M hM z) = 1 := by
  rw [residueGrid_decompose M hM z, phaseProb_add_int, phaseProb_grid hM]
  simp

theorem phase_good_mass_one {M : ℕ} (hM : 2 < M) (ω : ℝ) :
    8 / π ^ 2 ≤ ∑ y ∈ Finset.univ.filter
      (fun y : Fin M => circDist ω ((y : ℕ) / M) ≤ 1 / M), phaseProb M ω y := by
  classical
  have hm : 0 < M := by omega
  have hmr : (0 : ℝ) < M := by exact_mod_cast hm
  let z : ℤ := ⌊(M : ℝ) * ω⌋
  let t : ℝ := Int.fract ((M : ℝ) * ω)
  have ht : 0 ≤ t := Int.fract_nonneg _
  have ht1 : t < 1 := Int.fract_lt_one _
  have he : ω = ((z : ℝ) + t) / M := by
    apply (eq_div_iff hmr.ne').mpr
    have h := Int.fract_add_floor ((M : ℝ) * ω)
    dsimp [z, t]
    linarith
  let E := Finset.univ.filter (fun y : Fin M => circDist ω ((y : ℕ) / M) ≤ 1 / M)
  have hmem0 : residueGrid M hm z ∈ E := by
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [he]
    exact (residue_distance_le M hm z t).trans
      (div_le_div_of_nonneg_right (by simpa only [abs_of_nonneg ht] using ht1.le) hmr.le)
  have hpnn : ∀ y ∈ E, 0 ≤ phaseProb M ω y := fun y _ => phaseProb_nonneg M ω y
  by_cases ht0 : t = 0
  · have he0 : ω = (z : ℝ) / M := by simpa only [ht0, add_zero] using he
    have hp := Finset.single_le_sum hpnn hmem0
    rw [he0, phaseProb_integer_grid hm] at hp
    rw [← he0] at hp
    have h8 : 8 / π ^ 2 ≤ (1 : ℝ) := by
      apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
      nlinarith [Real.pi_gt_three]
    exact h8.trans hp
  · have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have he1 : ω = (((z + 1 : ℤ) : ℝ) + (t - 1)) / M := by
      rw [he]
      push_cast
      ring
    have hmem1 : residueGrid M hm (z + 1) ∈ E := by
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [he1]
      exact (residue_distance_le M hm (z + 1) (t - 1)).trans
        (div_le_div_of_nonneg_right (by rw [abs_of_neg (by linarith)]; linarith) hmr.le)
    have hne := residueGrid_consecutive_ne M (by omega) z
    have hs : ({residueGrid M hm z, residueGrid M hm (z + 1)} : Finset (Fin M)) ⊆ E := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hmem0
      · exact hmem1
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg hs
      (fun y hy _ => hpnn y hy)
    simp only [Finset.sum_pair hne] at hsum
    have hb := nearest_pair_probability M hM z t htp ht1
    rw [← he] at hb
    exact hb.trans hsum

end QAmpEst.Est.AEFresh
end
end


section

namespace QAmpEst.Est.AEFresh
open scoped Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem estimate_mass_mixture (M : ℕ) (hM : 0 < M) (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (χ : ι → Bool) (z0 : ι) (k : ℕ) :
    (∑ y ∈ estimateEvent (succProb A χ z0) M k, outcomeProb M A χ z0 y) =
      ((∑ y ∈ estimateEvent (succProb A χ z0) M k,
          phaseProb M (theta (succProb A χ z0)/π) y) +
        (∑ y ∈ estimateEvent (succProb A χ z0) M k,
          phaseProb M (-theta (succProb A χ z0)/π) y))/2 := by
  simp_rw [outcomeProb_mixture_all M hM A hA χ z0]
  rw [← Finset.sum_div, Finset.sum_add_distrib]

theorem native_confidence_one (M : ℕ) (hM : 0 < M) (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (χ : ι → Bool) (z0 : ι) :
    8/π^2 ≤ ∑y∈estimateEvent (succProb A χ z0) M 1,outcomeProb M A χ z0 y := by
  have hab := succProb_bounds A hA χ z0
  by_cases hM2 : M ≤ 2
  · rw [small_M_event_univ _ hab.1 hab.2 M hM hM2 1 (by omega), outcomeProb_sum M hM A hA]
    apply (div_le_one (sq_pos_of_pos Real.pi_pos)).mpr
    nlinarith [Real.pi_gt_three]
  have hM3 : 2 < M := by omega
  have hp (θ : ℝ) (hθ : θ=theta (succProb A χ z0) ∨ θ=-theta (succProb A χ z0)) :
      8/π^2 ≤ ∑y∈estimateEvent (succProb A χ z0) M 1,phaseProb M (θ/π) y := by
    have h := phase_good_mass_one hM3 (θ/π)
    have hh : 8/π^2 ≤ ∑y∈phaseEvent (θ/π) M 1,phaseProb M (θ/π) y := by
      simpa only [phaseEvent,Nat.cast_one,circDist_symm] using h
    exact hh.trans (phase_mass_transfer _ hab.1 hab.2 M hM 1 θ hθ _ (phaseProb_nonneg M _))
  have hplus := hp _ (Or.inl rfl)
  have hminus := hp _ (Or.inr rfl)
  rw [estimate_mass_mixture M hM A hA]
  linarith

theorem native_confidence_many (M : ℕ) (hM : 0 < M) (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (χ : ι → Bool) (z0 : ι) (k : ℕ) (hk : 2 ≤ k) :
    1-1/(2*((k:ℝ)-1)) < ∑y∈estimateEvent (succProb A χ z0) M k,outcomeProb M A χ z0 y := by
  have hab := succProb_bounds A hA χ z0
  have hp (θ : ℝ) (hθ : θ=theta (succProb A χ z0) ∨ θ=-theta (succProb A χ z0)) :
      1-1/(2*((k:ℝ)-1)) < ∑y∈estimateEvent (succProb A χ z0) M k,phaseProb M (θ/π) y := by
    have h := phase_good_mass_strict hM (θ/π) k hk
    have hh : 1-1/(2*((k:ℝ)-1)) < ∑y∈phaseEvent (θ/π) M k,phaseProb M (θ/π) y := by
      simpa only [phaseEvent,circDist_symm] using h
    exact hh.trans_le (phase_mass_transfer _ hab.1 hab.2 M hM k θ hθ _ (phaseProb_nonneg M _))
  have hplus := hp _ (Or.inl rfl)
  have hminus := hp _ (Or.inr rfl)
  rw [estimate_mass_mixture M hM A hA]
  linarith

end QAmpEst.Est.AEFresh
end


section

namespace QAmpEst.Est.AEFresh
open scoped Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exact_zero_output (M : ℕ) (hM : 0 < M) (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (χ : ι → Bool) (z0 : ι)
    (ha : succProb A χ z0 = 0) :
    ∑ y ∈ Finset.univ.filter (fun y : Fin M => estimate M y = 0), outcomeProb M A χ z0 y = 1 := by
  let l : Fin M := ⟨0,hM⟩
  have he (y : Fin M) : outcomeProb M A χ z0 y = if y=l then 1 else 0 := by
    rw [outcomeProb_zero M hM A hA χ z0 ha]
    simpa [l] using phaseProb_grid hM l y
  have hl : estimate M l = 0 := by simp [estimate, l]
  simp_rw [he]
  simp [hl]

theorem exact_one_output (M : ℕ) (hM : 0 < M) (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (χ : ι → Bool) (z0 : ι)
    (ha : succProb A χ z0 = 1) (hEven : Even M) :
    ∑ y ∈ Finset.univ.filter (fun y : Fin M => estimate M y = 1), outcomeProb M A χ z0 y = 1 := by
  rcases hEven with ⟨n,hn⟩
  have hnlt : n < M := by omega
  let l : Fin M := ⟨n,hnlt⟩
  have hMp : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hr : ((l:ℕ):ℝ)/M = (1/2:ℝ) := by
    dsimp [l]
    apply (div_eq_iff hMp).mpr
    have hc : (M:ℝ) = (n:ℝ)+(n:ℝ) := by exact_mod_cast hn
    linarith
  have he (y : Fin M) : outcomeProb M A χ z0 y = if y=l then 1 else 0 := by
    rw [outcomeProb_one M hM A hA χ z0 ha, ← hr]
    exact phaseProb_grid hM l y
  have hl : estimate M l = 1 := by
    unfold estimate
    rw [mul_div_assoc, hr, show π*(1/2:ℝ) = π/2 by ring, Real.sin_pi_div_two]
    norm_num
  simp_rw [he]
  simp [hl]

end QAmpEst.Est.AEFresh
end


section

open scoped Real Kronecker

namespace QAmpEst.Est

/-- Theorem 12 (Amplitude Estimation), arXiv:quant-ph/0005055v1, p. 19: for any positive
integer `k`, the output `ã = sin²(πy/M)` of `Est_Amp(A, χ, M)` satisfies
`|ã − a| ≤ 2πk√(a(1 − a))/M + k²π²/M²` with probability at least `8/π²` when `k = 1` and with
probability greater than `1 − 1/(2(k − 1))` for `k ≥ 2`. If `a = 0` then `ã = 0` with
certainty, and if `a = 1` and `M` is even, then `ã = 1` with certainty.
(The query count "exactly `M` evaluations of `f`" is not formalized.) -/
theorem theorem_12 {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (χ : ι → Bool) (z0 : ι) (M : ℕ) (hM : 0 < M) (k : ℕ) (hk : 1 ≤ k) :
    let a := succProb A χ z0
    let P := outcomeProb M A χ z0
    let E := Finset.univ.filter (fun y : Fin M =>
      |estimate M y - a| ≤
        2 * π * (k : ℝ) * Real.sqrt (a * (1 - a)) / (M : ℝ) + (k : ℝ) ^ 2 * π ^ 2 / (M : ℝ) ^ 2)
    (k = 1 → 8 / π ^ 2 ≤ ∑ y ∈ E, P y) ∧
      (2 ≤ k → 1 - 1 / (2 * ((k : ℝ) - 1)) < ∑ y ∈ E, P y) ∧
      (a = 0 → ∑ y ∈ Finset.univ.filter (fun y : Fin M => estimate M y = 0), P y = 1) ∧
      (a = 1 → Even M →
        ∑ y ∈ Finset.univ.filter (fun y : Fin M => estimate M y = 1), P y = 1) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    subst k
    convert AEFresh.native_confidence_one M hM A hA χ z0 using 1
    congr 1
  · intro h
    convert AEFresh.native_confidence_many M hM A hA χ z0 k h using 1
    congr 1
  · exact AEFresh.exact_zero_output M hM A hA χ z0
  · exact AEFresh.exact_one_output M hM A hA χ z0

end QAmpEst.Est
end


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (χ : ι → Bool) (z0 : ι) (M : ℕ) (hM : 0 < M) (k : ℕ) (hk : 1 ≤ k) :
    let a := QAmpEst.Est.succProb A χ z0
    let P := QAmpEst.Est.outcomeProb M A χ z0
    let E := Finset.univ.filter (fun y : Fin M =>
      |QAmpEst.Est.estimate M y - a| ≤
        2 * π * (k : ℝ) * Real.sqrt (a * (1 - a)) / (M : ℝ) + (k : ℝ) ^ 2 * π ^ 2 / (M : ℝ) ^ 2)
    (k = 1 → 8 / π ^ 2 ≤ ∑ y ∈ E, P y) ∧
      (2 ≤ k → 1 - 1 / (2 * ((k : ℝ) - 1)) < ∑ y ∈ E, P y) ∧
      (a = 0 → ∑ y ∈ Finset.univ.filter (fun y : Fin M => QAmpEst.Est.estimate M y = 0), P y = 1) ∧
      (a = 1 → Even M →
        ∑ y ∈ Finset.univ.filter (fun y : Fin M => QAmpEst.Est.estimate M y = 1), P y = 1) := by
  exact QAmpEst.Est.theorem_12 A hA χ z0 M hM k hk
