-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P28.positivePart_trace_contraction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T02:28:30.629993+00:00
-- url     : https://prove2.me/submissions/67df9c91-e49e-4d7f-a088-4d8b72d2e04c

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

open scoped Matrix ComplexOrder MatrixOrder

lemma g53_cfc_trace {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g53_conj_eig {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    star (hY.eigenvectorUnitary : Matrix n n ℂ) * Y * (hY.eigenvectorUnitary : Matrix n n ℂ) =
      Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) := by
  have hs := hY.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have hu := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize (Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) : Matrix n n ℂ) = D at *
  subst hs
  calc star U * (U * D * star U) * U
      = (star U * U) * D * (star U * U) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu, one_mul, mul_one]

lemma g53_posPart_aux {n : Type} [Fintype n] [DecidableEq n] {A B U : Matrix n n ℂ} (lam : n → ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hU : U * star U = 1)
    (hD : star U * (A - B) * U = Matrix.diagonal (RCLike.ofReal ∘ lam)) :
    ∑ i, max (lam i) 0 ≤ A.trace.re := by
  have hA' := hA.conjTranspose_mul_mul_same U
  have hB' := hB.conjTranspose_mul_mul_same U
  have htr : A.trace = (Uᴴ * A * U).trace := by
    rw [Matrix.trace_mul_cycle, ← Matrix.star_eq_conjTranspose, hU, one_mul]
  rw [htr, Matrix.trace, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  have h1 : (Uᴴ * A * U) i i - (Uᴴ * B * U) i i = ((lam i : ℝ) : ℂ) := by
    have := congrArg (fun M => M i i) hD
    rw [Matrix.mul_sub, Matrix.sub_mul] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  have ha' : 0 ≤ ((Uᴴ * A * U) i i).re := (Complex.nonneg_iff.mp (hA'.diag_nonneg (i := i))).1
  have hb' : 0 ≤ ((Uᴴ * B * U) i i).re := (Complex.nonneg_iff.mp (hB'.diag_nonneg (i := i))).1
  have h2 := congrArg Complex.re h1
  simp only [Complex.sub_re, Complex.ofReal_re] at h2
  simp only [Matrix.diag]
  exact max_le (by linarith) ha'

lemma g53_parts {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma g53_cfc_psd {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma g53_posPart_le {n : Type} [Fintype n] [DecidableEq n] {Y A B : Matrix n n ℂ} (hY : Y.IsHermitian)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hYAB : Y = A - B) :
    (cfc (fun t : ℝ => max t 0) Y).trace.re ≤ A.trace.re := by
  rw [g53_cfc_trace hY, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hD := g53_conj_eig hY
  have hu := Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize hY.eigenvalues = lam at *
  subst hYAB
  exact g53_posPart_aux lam hA hB hu hD

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P28
open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem solution (rho sigma : Mat I) (hrho : rho.IsHermitian) (hsigma : sigma.IsHermitian)
    (Phi : Mat I →ₗ[ℂ] Mat J) (hpos : Positive Phi) (htp : TP Phi) (n : ℕ) (a : ℝ) :
    tr (positivePart (Phi rho - (Real.exp ((n : ℝ) * a) : ℂ) • Phi sigma)) ≤
      tr (positivePart (rho - (Real.exp ((n : ℝ) * a) : ℂ) • sigma)) := by
  set c : ℝ := Real.exp ((n : ℝ) * a)
  set X : Mat I := rho - (c : ℂ) • sigma
  have hX : X.IsHermitian := by
    unfold Matrix.IsHermitian
    simp [X, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hrho.eq, hsigma.eq]
  have hY : Phi rho - (c : ℂ) • Phi sigma = Phi X := by simp [X, map_sub, map_smul]
  set Xp : Mat I := cfc (fun t : ℝ => max t 0) X with hXp
  set Xm : Mat I := cfc (fun t : ℝ => max (-t) 0) X with hXm
  have hXpm : X = Xp - Xm := (g53_parts X hX).symm
  have hPp := hpos _ (g53_cfc_psd X (fun t : ℝ => max t 0) (fun t => le_max_right _ _))
  have hPm := hpos _ (g53_cfc_psd X (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _))
  have hYeq : Phi X = Phi Xp - Phi Xm := by
    conv_lhs => rw [hXpm]
    rw [map_sub]
  have hYH : (Phi X).IsHermitian := by
    rw [hYeq]; exact hPp.isHermitian.sub hPm.isHermitian
  rw [hY]
  unfold tr positivePart
  calc (cfc (fun t : ℝ => max t 0) (Phi X)).trace.re ≤ (Phi Xp).trace.re :=
        g53_posPart_le hYH hPp hPm hYeq
    _ = Xp.trace.re := by rw [htp]
