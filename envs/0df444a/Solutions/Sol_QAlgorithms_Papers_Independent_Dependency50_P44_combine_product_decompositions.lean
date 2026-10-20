-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P44.combine_product_decompositions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T02:56:17.107239+00:00
-- url     : https://prove2.me/submissions/acb29d61-251d-4e45-b17d-6357afbe9825

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P44

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

open Filter Topology

attribute [local instance] Classical.propDecidable

section G53Lib
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

lemma g53_traceNorm_herm {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    QAlgorithms.traceNorm X =
      (cfc (fun t : ℝ => max t 0) X).trace.re + (cfc (fun t : ℝ => max (-t) 0) X).trace.re := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  unfold QAlgorithms.traceNorm
  rw [hX.eq]
  have h1 : X * X = cfc (fun t : ℝ => t * t) X := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) X, cfc_id' ℝ X]
  rw [h1, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) X, ← Complex.add_re, ← Matrix.trace_add,
    ← cfc_add X (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
  congr 2
  apply cfc_congr
  intro t _
  simp only [Function.comp]
  rw [← sq, Real.sqrt_sq_eq_abs]
  rcases le_total t 0 with h | h
  · rw [abs_of_nonpos h]; simp [h]
  · rw [abs_of_nonneg h]; simp [h]

lemma g53_negPart_eq {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc (fun t : ℝ => max (-t) 0) X = cfc (fun t : ℝ => max t 0) (-X) := by
  by_cases hX : IsSelfAdjoint X
  · exact cfc_comp_neg (f := fun t : ℝ => max t 0) (a := X)
  · have : ¬ IsSelfAdjoint (-X) := fun h => hX (by simpa using h.neg)
    rw [cfc_apply_of_not_predicate X hX, cfc_apply_of_not_predicate (-X) this]

/-- trace-norm triangle inequality for Hermitian matrices -/
lemma g53_traceNorm_add_le {n : Type} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    QAlgorithms.traceNorm (X + Y) ≤ QAlgorithms.traceNorm X + QAlgorithms.traceNorm Y := by
  have hXY : (X + Y).IsHermitian := hX.add hY
  rw [g53_traceNorm_herm hXY, g53_traceNorm_herm hX, g53_traceNorm_herm hY]
  have pX := g53_cfc_psd X (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have mX := g53_cfc_psd X (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have pY := g53_cfc_psd Y (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have mY := g53_cfc_psd Y (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have eX := g53_parts X hX
  have eY := g53_parts Y hY
  have e1 : X + Y = (cfc (fun t : ℝ => max t 0) X + cfc (fun t : ℝ => max t 0) Y) -
      (cfc (fun t : ℝ => max (-t) 0) X + cfc (fun t : ℝ => max (-t) 0) Y) := by
    conv_lhs => rw [← eX, ← eY]
    abel
  have e2 : -(X + Y) = (cfc (fun t : ℝ => max (-t) 0) X + cfc (fun t : ℝ => max (-t) 0) Y) -
      (cfc (fun t : ℝ => max t 0) X + cfc (fun t : ℝ => max t 0) Y) := by
    rw [e1]; abel
  have h1 := g53_posPart_le hXY (pX.add pY) (mX.add mY) e1
  have h2 := g53_posPart_le hXY.neg (mX.add mY) (pX.add pY) e2
  rw [← g53_negPart_eq] at h2
  rw [Matrix.trace_add, Complex.add_re] at h1 h2
  linarith

lemma g53d_tn_le {n : Type} [Fintype n] [DecidableEq n] {Y A B : Matrix n n ℂ} (hY : Y.IsHermitian)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hYAB : Y = A - B) :
    QAlgorithms.traceNorm Y ≤ A.trace.re + B.trace.re := by
  rw [g53_traceNorm_herm hY]
  have h1 := g53_posPart_le hY hA hB hYAB
  have h2 := g53_posPart_le hY.neg hB hA (by rw [hYAB]; abel)
  rw [← g53_negPart_eq] at h2
  linarith

lemma g53d_tn_neg {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    QAlgorithms.traceNorm (-X) = QAlgorithms.traceNorm X := by
  unfold QAlgorithms.traceNorm
  simp [Matrix.conjTranspose_neg]

lemma g53d_traceLeft_sub {α β : Type} [Fintype α] (M N : Matrix (α × β) (α × β) ℂ) :
    QAlgorithms.traceLeft (M - N) = QAlgorithms.traceLeft M - QAlgorithms.traceLeft N := by
  ext b b'
  simp [QAlgorithms.traceLeft, Finset.sum_sub_distrib]

lemma g53d_traceLeft_herm {α β : Type} [Fintype α] {M : Matrix (α × β) (α × β) ℂ}
    (hM : M.IsHermitian) : (QAlgorithms.traceLeft M).IsHermitian := by
  ext b b'
  simp only [Matrix.conjTranspose_apply, QAlgorithms.traceLeft, Matrix.of_apply, star_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Matrix.conjTranspose_apply, hM.eq]

lemma g53d_traceLeft_trace {α β : Type} [Fintype α] [Fintype β] (M : Matrix (α × β) (α × β) ℂ) :
    (QAlgorithms.traceLeft M).trace = M.trace := by
  simp only [Matrix.trace, QAlgorithms.traceLeft, Matrix.diag, Matrix.of_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

lemma g53d_traceLeft_psd {α β : Type} [Fintype α] [Fintype β] {M : Matrix (α × β) (α × β) ℂ}
    (hM : M.PosSemidef) : (QAlgorithms.traceLeft M).PosSemidef := by
  classical
  have : QAlgorithms.traceLeft M = ∑ a : α, M.submatrix (fun b => (a, b)) (fun b => (a, b)) := by
    ext b b'
    simp [QAlgorithms.traceLeft, Matrix.sum_apply]
  rw [this]
  exact Matrix.posSemidef_sum _ (fun a _ => hM.submatrix _)

lemma g53d_tn_traceLeft {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {Y : Matrix (α × β) (α × β) ℂ} (hY : Y.IsHermitian) :
    QAlgorithms.traceNorm (QAlgorithms.traceLeft Y) ≤ QAlgorithms.traceNorm Y := by
  have pY := g53_cfc_psd Y (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have mY := g53_cfc_psd Y (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have eY := g53_parts Y hY
  have h := g53d_tn_le (g53d_traceLeft_herm hY) (g53d_traceLeft_psd pY) (g53d_traceLeft_psd mY)
    (by rw [← g53d_traceLeft_sub, eY])
  rw [g53d_traceLeft_trace, g53d_traceLeft_trace] at h
  rw [g53_traceNorm_herm hY]
  exact h

lemma g53d_tn_kron {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {X : Matrix β β ℂ} {σ : Matrix α α ℂ} (hσ : σ.PosSemidef) (hσt : σ.trace = 1)
    (hX : X.IsHermitian) :
    QAlgorithms.traceNorm (Matrix.kronecker σ X) ≤ QAlgorithms.traceNorm X := by
  have pX := g53_cfc_psd X (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have mX := g53_cfc_psd X (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have eX := g53_parts X hX
  have hK : (Matrix.kronecker σ X).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.kronecker, Matrix.conjTranspose_kronecker, hσ.1.eq, hX.eq]
  have h := g53d_tn_le hK (hσ.kronecker pX) (hσ.kronecker mX)
    (by conv_lhs => rw [← eX]
        ext i j; simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_sub])
  rw [Matrix.trace_kronecker, Matrix.trace_kronecker, hσt, one_mul, one_mul] at h
  rw [g53_traceNorm_herm hX]
  exact h

lemma g53d_kron_herm {α β : Type} {σ : Matrix α α ℂ} {X : Matrix β β ℂ}
    (hσ : σ.IsHermitian) (hX : X.IsHermitian) : (Matrix.kronecker σ X).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.kronecker, Matrix.conjTranspose_kronecker, hσ.eq, hX.eq]

lemma g53d_kron_sub_right {α β : Type} (σ : Matrix α α ℂ) (X Y : Matrix β β ℂ) :
    Matrix.kronecker σ (X - Y) = Matrix.kronecker σ X - Matrix.kronecker σ Y := by
  ext i j; simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_sub]

end G53Lib

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P44

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

/-- PDF p.4, Lemma 1: combining two normalized approximate product decompositions.
The B state in the conclusion is the computed marginal of tau, not an independent parameter. -/
theorem solution {A B C : Type}
    [Fintype A] [Fintype B] [Fintype C] [Nonempty A] [Nonempty B] [Nonempty C]
    (rho : Operator (A × (B × C))) (sigma : Operator A) (omega : Operator (B × C))
    (tau : Operator (A × B)) (eta : Operator C)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (homega : IsDensityMatrix omega) (htau : IsDensityMatrix tau) (heta : IsDensityMatrix eta)
    (eps1 eps2 : ℝ)
    (h1 : traceNorm (rho - Matrix.kronecker sigma omega) ≤ eps1)
    (h2 : traceNorm (rho - (show Operator (A × (B × C)) from
      fun x y => Matrix.kronecker tau eta
        ((x.1, x.2.1), x.2.2) ((y.1, y.2.1), y.2.2))) ≤ eps2) :
    traceNorm (rho - Matrix.kronecker sigma (Matrix.kronecker (traceLeft tau) eta)) ≤
      2 * eps1 + eps2 := by
  have hKl : traceLeft (show Operator (A × (B × C)) from
      fun x y => Matrix.kronecker tau eta
        ((x.1, x.2.1), x.2.2) ((y.1, y.2.1), y.2.2)) = Matrix.kronecker (traceLeft tau) eta := by
    ext ⟨b, c⟩ ⟨b', c'⟩
    simp [traceLeft, Matrix.kronecker, Matrix.kroneckerMap_apply, Finset.sum_mul]
  have hKh : (show Operator (A × (B × C)) from
      fun x y => Matrix.kronecker tau eta
        ((x.1, x.2.1), x.2.2) ((y.1, y.2.1), y.2.2)).IsHermitian :=
    (g53d_kron_herm htau.1.1 heta.1.1).submatrix (fun x : A × (B × C) => ((x.1, x.2.1), x.2.2))
  generalize (show Operator (A × (B × C)) from
      fun x y => Matrix.kronecker tau eta
        ((x.1, x.2.1), x.2.2) ((y.1, y.2.1), y.2.2)) = K at hKl hKh h2
  have hso : traceLeft (Matrix.kronecker sigma omega) = omega := by
    have : ∑ a, sigma a a = 1 := hsigma.2
    ext b b'
    simp [traceLeft, Matrix.kronecker, Matrix.kroneckerMap_apply, ← Finset.sum_mul, this]
  have hρ := hrho.1.1
  have hso_h := g53d_kron_herm hsigma.1.1 homega.1.1
  have hZh : (omega - Matrix.kronecker (traceLeft tau) eta).IsHermitian :=
    homega.1.1.sub (g53d_kron_herm (g53d_traceLeft_herm htau.1.1) heta.1.1)
  have e1 : rho - Matrix.kronecker sigma (Matrix.kronecker (traceLeft tau) eta) =
      (rho - Matrix.kronecker sigma omega) +
        Matrix.kronecker sigma (omega - Matrix.kronecker (traceLeft tau) eta) := by
    rw [g53d_kron_sub_right]; abel
  have e2 : omega - Matrix.kronecker (traceLeft tau) eta =
      -(traceLeft (rho - Matrix.kronecker sigma omega)) + traceLeft (rho - K) := by
    rw [g53d_traceLeft_sub, g53d_traceLeft_sub, hso, hKl]; abel
  have i1 := g53_traceNorm_add_le (hρ.sub hso_h) (g53d_kron_herm hsigma.1.1 hZh)
  have i2 := g53d_tn_kron hsigma.1 hsigma.2 hZh
  have i3 := g53_traceNorm_add_le (g53d_traceLeft_herm (hρ.sub hso_h)).neg
    (g53d_traceLeft_herm (hρ.sub hKh))
  rw [g53d_tn_neg] at i3
  have i4 := g53d_tn_traceLeft (hρ.sub hso_h)
  have i5 := g53d_tn_traceLeft (hρ.sub hKh)
  rw [← e2] at i3
  rw [← e1] at i1
  linarith

end
