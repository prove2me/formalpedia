-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P18.classicalFidelityBound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:23:32.213338+00:00
-- url     : https://prove2.me/submissions/20476c5c-9f1c-4f33-b4d4-7943010c7247

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

/-- Diagonal of a Hermitian matrix is dominated by the diagonal of its square. -/
lemma x8_diag_sq {ι : Type} [Fintype ι] (S : Matrix ι ι ℂ) (hS : S.IsHermitian) (i : ι) :
    (S i i).re ^ 2 ≤ ((S * S) i i).re := by
  have h1 : (S * S) i i = ∑ k, ((Complex.normSq (S i k) : ℝ) : ℂ) := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have : S k i = star (S i k) := by
      rw [← Matrix.conjTranspose_apply, hS.eq]
    rw [this, Complex.star_def, Complex.mul_conj]
  rw [h1, Complex.re_sum]
  simp only [Complex.ofReal_re]
  calc (S i i).re ^ 2 ≤ Complex.normSq (S i i) := by
        rw [Complex.normSq_apply]; nlinarith [sq_nonneg (S i i).im]
    _ ≤ ∑ k, Complex.normSq (S i k) :=
        Finset.single_le_sum (f := fun k => Complex.normSq (S i k))
          (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

lemma x8_sqrt_mul {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (h : M.PosSemidef) :
    cfc Real.sqrt M * cfc Real.sqrt M = M ∧ (cfc Real.sqrt M).PosSemidef := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ M := Matrix.nonneg_iff_posSemidef.2 h
  constructor
  · rw [← cfc_mul (fun x => Real.sqrt x) (fun x => Real.sqrt x) M]
    conv_rhs => rw [← cfc_id' ℝ M]
    apply cfc_congr
    intro x hx
    exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg h0 hx)
  · open scoped MatrixOrder in
    exact Matrix.nonneg_iff_posSemidef.1 (cfc_nonneg (fun x _ => Real.sqrt_nonneg x))

/-- uniqueness of the PSD square root -/
lemma x8_sqrt_unique {ι : Type} [Fintype ι] [DecidableEq ι] (M R : Matrix ι ι ℂ)
    (hM : M.PosSemidef) (hR : R.PosSemidef) (hRR : R * R = M) : cfc Real.sqrt M = R := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ M := Matrix.nonneg_iff_posSemidef.2 hM
  open scoped MatrixOrder in
  have h1 : 0 ≤ R := Matrix.nonneg_iff_posSemidef.2 hR
  open scoped MatrixOrder in
  have := CFC.sqrt_eq_real_sqrt M h0
  open scoped MatrixOrder in
  rw [cfcₙ_eq_cfc] at this
  rw [← this]
  open scoped MatrixOrder in
  exact CFC.sqrt_unique hRR h1

def x8r (d : ℕ) : Fin d × Fin d → ℂ :=
  fun i => if i.1 = i.2 then ((Real.sqrt (1 / (d : ℝ)) : ℝ) : ℂ) else 0

lemma x8_target (d : ℕ) :
    classicalTarget d = Matrix.diagonal (fun i => x8r d i * x8r d i) := by
  ext i j
  simp only [classicalTarget, Matrix.diagonal_apply, x8r]
  by_cases hij : i = j
  · subst hij
    by_cases h : i.1 = i.2
    · simp only [h, and_self, if_true]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
      push_cast; ring
    · simp [h]
  · simp [hij]

lemma x8_R_psd (d : ℕ) : (Matrix.diagonal (x8r d)).PosSemidef := by
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  simp only [x8r]
  split_ifs
  · exact Complex.zero_le_real.2 (Real.sqrt_nonneg _)
  · exact le_refl _

lemma x8_sqrt_target (d : ℕ) : cfc Real.sqrt (classicalTarget d) = Matrix.diagonal (x8r d) := by
  apply x8_sqrt_unique
  · rw [x8_target, Matrix.posSemidef_diagonal_iff]
    intro i
    simp only [x8r]
    split_ifs
    · rw [← Complex.ofReal_mul]; exact Complex.zero_le_real.2 (mul_self_nonneg _)
    · simp
  · exact x8_R_psd d
  · rw [x8_target, Matrix.diagonal_mul_diagonal]

/-- root fidelity bound by the diagonal -/
lemma x8_rf_le (d : ℕ) (sigma : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hsigma : sigma.PosSemidef) :
    0 ≤ QAlgorithms.rootFidelity (classicalTarget d) sigma ∧
    QAlgorithms.rootFidelity (classicalTarget d) sigma ≤
      ∑ m : Fin d, Real.sqrt ((sigma (m, m) (m, m)).re / d) := by
  unfold QAlgorithms.rootFidelity
  rw [x8_sqrt_target]
  set R := Matrix.diagonal (x8r d)
  have hRpsd := x8_R_psd d
  have hM : (R * sigma * R).PosSemidef := by
    have := hsigma.conjTranspose_mul_mul_same R
    rwa [hRpsd.1.eq] at this
  obtain ⟨hSS, hSpsd⟩ := x8_sqrt_mul _ hM
  set S := cfc Real.sqrt (R * sigma * R)
  have hdiag : ∀ i, (S i i).re ≤ Real.sqrt (((R * sigma * R) i i).re) := by
    intro i
    have := x8_diag_sq S hSpsd.1 i
    rw [hSS] at this
    have hnn : 0 ≤ (S i i).re := by
      have := hSpsd.diag_nonneg (i := i)
      exact (Complex.nonneg_iff.1 this).1
    exact Real.le_sqrt_of_sq_le this
  have hMii : ∀ i : Fin d × Fin d, ((R * sigma * R) i i).re =
      if i.1 = i.2 then (sigma i i).re / d else 0 := by
    intro i
    simp only [R, Matrix.mul_diagonal, Matrix.diagonal_mul, x8r]
    split_ifs with h
    · rw [show ((Real.sqrt (1 / (d : ℝ)) : ℂ)) * sigma i i * (Real.sqrt (1 / (d : ℝ)) : ℂ)
          = ((Real.sqrt (1 / (d : ℝ)) * Real.sqrt (1 / (d : ℝ)) : ℝ) : ℂ) * sigma i i by
            push_cast; ring]
      rw [Real.mul_self_sqrt (by positivity), Complex.re_ofReal_mul]
      ring
    · simp
  have htr : (S.trace).re = ∑ i, (S i i).re := by
    rw [Matrix.trace, Complex.re_sum]; rfl
  rw [htr]
  constructor
  · exact Finset.sum_nonneg (fun i _ => (Complex.nonneg_iff.1 (hSpsd.diag_nonneg (i := i))).1)
  calc ∑ i, (S i i).re ≤ ∑ i, Real.sqrt (((R * sigma * R) i i).re) :=
        Finset.sum_le_sum (fun i _ => hdiag i)
    _ = ∑ i : Fin d × Fin d, if i.1 = i.2 then Real.sqrt ((sigma i i).re / d) else 0 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hMii]; split_ifs <;> simp
    _ = ∑ m : Fin d, Real.sqrt ((sigma (m, m) (m, m)).re / d) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Finset.sum_ite_eq]
        simp

lemma x8_amgm {d : ℕ} (x y : Fin d → ℝ) (hxy : ∀ a b, 0 ≤ x a * y b) :
    (∑ m, Real.sqrt (x m * y m)) ^ 2 ≤ (∑ a, x a) * (∑ b, y b) := by
  rw [sq, Finset.sum_mul_sum, Finset.sum_mul_sum]
  have key : ∀ m n, Real.sqrt (x m * y m) * Real.sqrt (x n * y n) ≤
      (x m * y n + x n * y m) / 2 := by
    intro m n
    rw [← Real.sqrt_mul (hxy m m), show x m * y m * (x n * y n) = (x m * y n) * (x n * y m) by ring]
    have h1 := hxy m n; have h2 := hxy n m
    calc Real.sqrt ((x m * y n) * (x n * y m)) ≤ Real.sqrt (((x m * y n + x n * y m) / 2) ^ 2) := by
          apply Real.sqrt_le_sqrt; nlinarith [sq_nonneg (x m * y n - x n * y m)]
      _ = _ := Real.sqrt_sq (by linarith)
  calc ∑ m, ∑ n, Real.sqrt (x m * y m) * Real.sqrt (x n * y n)
      ≤ ∑ m, ∑ n, (x m * y n + x n * y m) / 2 :=
        Finset.sum_le_sum (fun m _ => Finset.sum_le_sum (fun n _ => key m n))
    _ = ∑ a, ∑ b, x a * y b := by
        simp only [add_div, Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun m n => x n * y m / 2)]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        ring

lemma x8_feasible_bound (d : ℕ) (hd : 0 < d) (sigma : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hsigma : sigma.PosSemidef) (k l : Matrix (Fin d) (Fin d) ℂ) (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hf : GammaFeasible sigma k l v) :
    QAlgorithms.Papers.Independent.Information100.P67.squaredFidelity (classicalTarget d) sigma * d ≤
      (Matrix.kronecker k l).trace.re := by
  obtain ⟨hk, hl, hv, h1, h2, h3, h4⟩ := hf
  set x : Fin d → ℝ := fun a => (k a a).re
  set y : Fin d → ℝ := fun b => (l b b).re
  have hkim : ∀ a, (k a a).im = 0 := fun a => by
    have := congrFun (congrFun hk.eq a) a
    rw [Matrix.conjTranspose_apply] at this
    exact Complex.conj_eq_iff_im.1 this
  have hlim : ∀ a, (l a a).im = 0 := fun a => by
    have := congrFun (congrFun hl.eq a) a
    rw [Matrix.conjTranspose_apply] at this
    exact Complex.conj_eq_iff_im.1 this
  have hkl : ∀ a b, ((Matrix.kronecker k l) (a, b) (a, b)).re = x a * y b := by
    intro a b
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Complex.mul_re, hkim, hlim, x, y]
    ring
  -- k ⊗ l is PSD
  have hxy : ∀ a b, 0 ≤ x a * y b := by
    intro a b
    have e1 := (Complex.nonneg_iff.1 (h3.diag_nonneg (i := (a, b)))).1
    have e2 := (Complex.nonneg_iff.1 (h4.diag_nonneg (i := (a, b)))).1
    simp only [Matrix.add_apply, Matrix.sub_apply, Complex.add_re, Complex.sub_re] at e1 e2
    rw [← hkl]; linarith
  have hsm : ∀ m, (sigma (m, m) (m, m)).re ≤ x m * y m := by
    intro m
    have e2 := (Complex.nonneg_iff.1 (h2.diag_nonneg (i := (m, m)))).1
    have e4 := (Complex.nonneg_iff.1 (h4.diag_nonneg (i := (m, m)))).1
    simp only [QAlgorithms.Papers.Independent.Information100.P04.gamma, Matrix.sub_apply,
      Complex.sub_re] at e2 e4
    rw [← hkl]; linarith
  have htr : (Matrix.kronecker k l).trace.re = (∑ a, x a) * (∑ b, y b) := by
    rw [Matrix.trace, Complex.re_sum, Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    exact hkl a b
  obtain ⟨h0, hle⟩ := x8_rf_le d sigma hsigma
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hb : QAlgorithms.rootFidelity (classicalTarget d) sigma ≤
      Real.sqrt (1 / d) * ∑ m, Real.sqrt (x m * y m) := by
    refine hle.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun m _ => ?_)
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [div_eq_mul_inv, one_div, mul_comm]
    exact mul_le_mul_of_nonneg_left (hsm m) (by positivity)
  unfold QAlgorithms.Papers.Independent.Information100.P67.squaredFidelity
  rw [htr]
  have hs := pow_le_pow_left₀ h0 hb 2
  rw [mul_pow, Real.sq_sqrt (by positivity)] at hs
  have := x8_amgm x y hxy
  calc QAlgorithms.rootFidelity (classicalTarget d) sigma ^ 2 * d
      ≤ 1 / d * (∑ m, Real.sqrt (x m * y m)) ^ 2 * d := by gcongr
    _ = (∑ m, Real.sqrt (x m * y m)) ^ 2 := by field_simp
    _ ≤ _ := this

theorem x8_main (d : ℕ) (hd : 0 < d)
    (sigma : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hsigma : sigma.PosSemidef) (hgamma : correlationGauge sigma ≤ 1) :
    QAlgorithms.Papers.Independent.Information100.P67.squaredFidelity (classicalTarget d) sigma ≤ 1 / (d : ℝ) := by
  set F := QAlgorithms.Papers.Independent.Information100.P67.squaredFidelity (classicalTarget d) sigma
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hlb : ((F * d : ℝ) : EReal) ≤ correlationGauge sigma := by
    unfold correlationGauge
    apply le_sInf
    rintro r ⟨k, l, v, hf, rfl⟩
    exact EReal.coe_le_coe_iff.2 (x8_feasible_bound d hd sigma hsigma k l v hf)
  have h1 : F * d ≤ 1 := by
    have := hlb.trans hgamma
    exact_mod_cast this
  rw [le_div_iff₀ hdpos]; linarith

end QAlgorithms.Papers.Independent.Dependency50.P18

open QAlgorithms.Papers.Independent.Dependency50.P18 in
open scoped ComplexOrder in
attribute [local instance] Classical.propDecidable in
theorem solution (d : ℕ) (hd : 0 < d)
    (sigma : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hsigma : sigma.PosSemidef) (hgamma : correlationGauge sigma ≤ 1) :
    QAlgorithms.Papers.Independent.Information100.P67.squaredFidelity (classicalTarget d) sigma ≤ 1 / (d : ℝ) :=
  x8_main d hd sigma hsigma hgamma
