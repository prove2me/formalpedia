-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.tensorPerturbation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:35:11.784599+00:00
-- url     : https://prove2.me/submissions/77a61b05-801e-4685-9132-4914580cfd00

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open scoped MatrixOrder
lemma g79a_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g79a_conj_eig {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
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

lemma g79a_posPart_aux {n : Type*} [Fintype n] [DecidableEq n] {A B U : Matrix n n ℂ} (lam : n → ℝ)
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

lemma g79a_parts {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma g79a_cfc_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma g79a_posPart_le {n : Type*} [Fintype n] [DecidableEq n] {Y A B : Matrix n n ℂ} (hY : Y.IsHermitian)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hYAB : Y = A - B) :
    (cfc (fun t : ℝ => max t 0) Y).trace.re ≤ A.trace.re := by
  rw [g79a_cfc_trace hY, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hD := g79a_conj_eig hY
  have hu := Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize hY.eigenvalues = lam at *
  subst hYAB
  exact g79a_posPart_aux lam hA hB hu hD

lemma g79a_traceNorm_herm {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
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

lemma g79a_negPart_eq {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc (fun t : ℝ => max (-t) 0) X = cfc (fun t : ℝ => max t 0) (-X) := by
  by_cases hX : IsSelfAdjoint X
  · exact cfc_comp_neg (f := fun t : ℝ => max t 0) (a := X)
  · have : ¬ IsSelfAdjoint (-X) := fun h => hX (by simpa using h.neg)
    rw [cfc_apply_of_not_predicate X hX, cfc_apply_of_not_predicate (-X) this]

/-- trace-norm triangle inequality for Hermitian matrices -/
lemma g79a_traceNorm_add_le {n : Type*} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    QAlgorithms.traceNorm (X + Y) ≤ QAlgorithms.traceNorm X + QAlgorithms.traceNorm Y := by
  have hXY : (X + Y).IsHermitian := hX.add hY
  rw [g79a_traceNorm_herm hXY, g79a_traceNorm_herm hX, g79a_traceNorm_herm hY]
  have pX := g79a_cfc_psd X (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have mX := g79a_cfc_psd X (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have pY := g79a_cfc_psd Y (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have mY := g79a_cfc_psd Y (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have eX := g79a_parts X hX
  have eY := g79a_parts Y hY
  have e1 : X + Y = (cfc (fun t : ℝ => max t 0) X + cfc (fun t : ℝ => max t 0) Y) -
      (cfc (fun t : ℝ => max (-t) 0) X + cfc (fun t : ℝ => max (-t) 0) Y) := by
    conv_lhs => rw [← eX, ← eY]
    abel
  have e2 : -(X + Y) = (cfc (fun t : ℝ => max (-t) 0) X + cfc (fun t : ℝ => max (-t) 0) Y) -
      (cfc (fun t : ℝ => max t 0) X + cfc (fun t : ℝ => max t 0) Y) := by
    rw [e1]; abel
  have h1 := g79a_posPart_le hXY (pX.add pY) (mX.add mY) e1
  have h2 := g79a_posPart_le hXY.neg (mX.add mY) (pX.add pY) e2
  rw [← g79a_negPart_eq] at h2
  rw [Matrix.trace_add, Complex.add_re] at h1 h2
  linarith


lemma g79a_tn_le_sub {n : Type*} [Fintype n] [DecidableEq n] {Y A B : Matrix n n ℂ}
    (hY : Y.IsHermitian) (hA : A.PosSemidef) (hB : B.PosSemidef) (h : Y = A - B) :
    QAlgorithms.traceNorm Y ≤ A.trace.re + B.trace.re := by
  rw [g79a_traceNorm_herm hY]
  have h1 := g79a_posPart_le hY hA hB h
  have h2 := g79a_posPart_le hY.neg hB hA (by rw [h]; abel)
  rw [← g79a_negPart_eq] at h2
  linarith

lemma g79a_herm_kron {I J : Type*} {X : Matrix I I ℂ} {Y : Matrix J J ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) : (Matrix.kronecker X Y).IsHermitian := by
  unfold Matrix.IsHermitian Matrix.kronecker
  rw [Matrix.conjTranspose_kronecker, hX.eq, hY.eq]

lemma g79a_sub_kron {I J : Type*} (A B : Matrix I I ℂ) (C : Matrix J J ℂ) :
    Matrix.kronecker (A - B) C = Matrix.kronecker A C - Matrix.kronecker B C := by
  ext a b; simp [Matrix.kroneckerMap_apply, sub_mul]

lemma g79a_kron_sub {I J : Type*} (C : Matrix I I ℂ) (A B : Matrix J J ℂ) :
    Matrix.kronecker C (A - B) = Matrix.kronecker C A - Matrix.kronecker C B := by
  ext a b; simp [Matrix.kroneckerMap_apply, mul_sub]

lemma g79a_tn_kron_left {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {X : Matrix I I ℂ} {ρ : Matrix J J ℂ} (hX : X.IsHermitian) (hρ : IsDensityMatrix ρ) :
    QAlgorithms.traceNorm (Matrix.kronecker X ρ) ≤ QAlgorithms.traceNorm X := by
  have hP := g79a_cfc_psd X (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have hN := g79a_cfc_psd X (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have e : Matrix.kronecker X ρ = Matrix.kronecker (cfc (fun t : ℝ => max t 0) X) ρ -
      Matrix.kronecker (cfc (fun t : ℝ => max (-t) 0) X) ρ := by
    rw [← g79a_sub_kron, g79a_parts X hX]
  have := g79a_tn_le_sub (g79a_herm_kron hX hρ.1.isHermitian) (hP.kronecker hρ.1)
    (hN.kronecker hρ.1) e
  rw [Matrix.trace_kronecker, Matrix.trace_kronecker, hρ.2, mul_one, mul_one] at this
  rw [g79a_traceNorm_herm hX]; exact this

lemma g79a_tn_kron_right {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {X : Matrix J J ℂ} {ρ : Matrix I I ℂ} (hX : X.IsHermitian) (hρ : IsDensityMatrix ρ) :
    QAlgorithms.traceNorm (Matrix.kronecker ρ X) ≤ QAlgorithms.traceNorm X := by
  have hP := g79a_cfc_psd X (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have hN := g79a_cfc_psd X (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have e : Matrix.kronecker ρ X = Matrix.kronecker ρ (cfc (fun t : ℝ => max t 0) X) -
      Matrix.kronecker ρ (cfc (fun t : ℝ => max (-t) 0) X) := by
    rw [← g79a_kron_sub, g79a_parts X hX]
  have := g79a_tn_le_sub (g79a_herm_kron hρ.1.isHermitian hX) (hρ.1.kronecker hP)
    (hρ.1.kronecker hN) e
  rw [Matrix.trace_kronecker, Matrix.trace_kronecker, hρ.2, one_mul, one_mul] at this
  rw [g79a_traceNorm_herm hX]; exact this

theorem g79a_trace_mul_psd_nonneg {X : Type*} [Fintype X] [DecidableEq X] (M ρ : Matrix X X ℂ)
    (hM : M.PosSemidef) (hρ : ρ.PosSemidef) : 0 ≤ (M * ρ).trace := by
  have h0 : 0 ≤ ρ := hρ.nonneg
  have hS2 : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self ρ h0
  have hSa : IsSelfAdjoint (CFC.sqrt ρ) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg ρ)
  have hSh : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := by
    rw [← Matrix.star_eq_conjTranspose]; exact hSa.star_eq
  have htr : (M * ρ).trace = (CFC.sqrt ρ * M * (CFC.sqrt ρ)ᴴ).trace := by
    rw [hSh]
    conv_lhs => rw [← hS2, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  rw [htr]
  exact (hM.mul_mul_conjTranspose_same (CFC.sqrt ρ)).trace_nonneg

lemma g79a_one_sub_psd {X : Type*} [Fintype X] [DecidableEq X] {σ : Matrix X X ℂ}
    (hσ : IsDensityMatrix σ) : (1 - σ).PosSemidef := by
  have hH := hσ.1.isHermitian
  have e : (1 : Matrix X X ℂ) - σ = cfc (fun t : ℝ => 1 - t) σ := by
    rw [cfc_sub (fun _ : ℝ => (1:ℝ)) (fun t : ℝ => t) σ, cfc_const_one ℝ σ, cfc_id' ℝ σ]
  rw [e, ← Matrix.nonneg_iff_posSemidef]
  apply cfc_nonneg
  intro t ht
  rw [hH.spectrum_real_eq_range_eigenvalues] at ht
  obtain ⟨i, rfl⟩ := ht
  have hs : ∑ j, hH.eigenvalues j = 1 := by
    have := hH.trace_eq_sum_eigenvalues
    rw [hσ.2] at this
    have h2 := congrArg Complex.re this
    simp at h2
    linarith
  have hle : hH.eigenvalues i ≤ ∑ j, hH.eigenvalues j :=
    Finset.single_le_sum (fun j _ => hσ.1.eigenvalues_nonneg j) (Finset.mem_univ i)
  linarith

lemma g79a_overlap {X : Type*} [Fintype X] [DecidableEq X] {ρ σ : Matrix X X ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    (ρ * σ).trace = (((ρ * σ).trace.re : ℝ) : ℂ) ∧ 0 ≤ (ρ * σ).trace.re ∧ (ρ * σ).trace.re ≤ 1 := by
  have h0 := g79a_trace_mul_psd_nonneg ρ σ hρ.1 hσ.1
  have h1 := g79a_trace_mul_psd_nonneg ρ (1 - σ) hρ.1 (g79a_one_sub_psd hσ)
  rw [Matrix.mul_sub, Matrix.trace_sub, mul_one, hρ.2] at h1
  rw [Complex.nonneg_iff] at h0 h1
  refine ⟨Complex.ext (by simp) (by simp; linarith [h0.2]), h0.1, ?_⟩
  simp at h1; linarith [h1.1]

/-- Unnumbered tensor inequalities, PDF p.8. All four factors are normalized. -/
theorem solution {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (rho1 sigma1 : Matrix I I ℂ) (rho2 sigma2 : Matrix J J ℂ)
    (hrho1 : IsDensityMatrix rho1) (hsigma1 : IsDensityMatrix sigma1)
    (hrho2 : IsDensityMatrix rho2) (hsigma2 : IsDensityMatrix sigma2) :
    traceNorm (Matrix.kronecker rho1 rho2 - Matrix.kronecker sigma1 sigma2) ≤
      traceNorm (rho1 - sigma1) + traceNorm (rho2 - sigma2) ∧
    1 - effectProb (Matrix.kronecker rho1 rho2) (Matrix.kronecker sigma1 sigma2) ≤
      (1 - effectProb rho1 sigma1) + (1 - effectProb rho2 sigma2) := by
  constructor
  · have e : Matrix.kronecker rho1 rho2 - Matrix.kronecker sigma1 sigma2 =
        Matrix.kronecker (rho1 - sigma1) rho2 + Matrix.kronecker sigma1 (rho2 - sigma2) := by
      rw [g79a_sub_kron, g79a_kron_sub]; abel
    have hd1 : (rho1 - sigma1).IsHermitian := hrho1.1.isHermitian.sub hsigma1.1.isHermitian
    have hd2 : (rho2 - sigma2).IsHermitian := hrho2.1.isHermitian.sub hsigma2.1.isHermitian
    rw [e]
    refine (g79a_traceNorm_add_le (g79a_herm_kron hd1 hrho2.1.isHermitian)
      (g79a_herm_kron hsigma1.1.isHermitian hd2)).trans ?_
    exact add_le_add (g79a_tn_kron_left hd1 hrho2) (g79a_tn_kron_right hd2 hsigma1)
  · obtain ⟨e1, a0, a1⟩ := g79a_overlap hrho1 hsigma1
    obtain ⟨e2, b0, b1⟩ := g79a_overlap hrho2 hsigma2
    have h : effectProb (Matrix.kronecker rho1 rho2) (Matrix.kronecker sigma1 sigma2) =
        effectProb rho1 sigma1 * effectProb rho2 sigma2 := by
      unfold effectProb Matrix.kronecker
      rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, e1, e2]
      simp
    rw [h]
    unfold effectProb
    nlinarith [mul_nonneg (sub_nonneg.2 a1) (sub_nonneg.2 b1)]


end

