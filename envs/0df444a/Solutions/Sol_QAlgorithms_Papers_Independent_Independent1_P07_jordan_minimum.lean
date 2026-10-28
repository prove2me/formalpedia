-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P07.jordan_minimum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:50:54.534207+00:00
-- url     : https://prove2.me/submissions/c38c6795-833e-4927-a7a9-4335a66b330b

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P07_Model
set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexOrder MatrixOrder

lemma g53_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g53_conj_eig {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
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

lemma g53_posPart_aux {n : Type*} [Fintype n] [DecidableEq n] {A B U : Matrix n n ℂ} (lam : n → ℝ)
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

lemma g53_parts {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma g53_cfc_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma g53_posPart_le {n : Type*} [Fintype n] [DecidableEq n] {Y A B : Matrix n n ℂ} (hY : Y.IsHermitian)
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

lemma g53_traceNorm_herm {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
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

lemma g53_negPart_eq {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc (fun t : ℝ => max (-t) 0) X = cfc (fun t : ℝ => max t 0) (-X) := by
  by_cases hX : IsSelfAdjoint X
  · exact cfc_comp_neg (f := fun t : ℝ => max t 0) (a := X)
  · have : ¬ IsSelfAdjoint (-X) := fun h => hX (by simpa using h.neg)
    rw [cfc_apply_of_not_predicate X hX, cfc_apply_of_not_predicate (-X) this]

/-- trace-norm triangle inequality for Hermitian matrices -/
lemma g53_traceNorm_add_le {n : Type*} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℂ}
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


lemma S180J_tn_psd {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    QAlgorithms.traceNorm P = P.trace.re := by
  rw [g53_traceNorm_herm hP.1]
  have hsp : ∀ x ∈ spectrum ℝ P, 0 ≤ x := fun x hx =>
    spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hP) hx
  have e1 : cfc (fun t : ℝ => max t 0) P = P := by
    conv_rhs => rw [← cfc_id' ℝ P]
    exact cfc_congr fun x hx => max_eq_left (hsp x hx)
  have e2 : cfc (fun t : ℝ => max (-t) 0) P = 0 := by
    rw [← cfc_zero ℝ P]
    exact cfc_congr fun x hx => max_eq_right (by linarith [hsp x hx])
  rw [e1, e2]; simp

lemma S180J_tn_neg {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) :
    QAlgorithms.traceNorm (-P) = QAlgorithms.traceNorm P := by
  unfold QAlgorithms.traceNorm; simp [Matrix.conjTranspose_neg]

lemma S180J_tr_real {n : Type*} [Fintype n] {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    0 ≤ P.trace.re ∧ P.trace = ((P.trace.re : ℝ) : ℂ) := by
  have h := hP.trace_nonneg
  rw [Complex.nonneg_iff] at h
  refine ⟨h.1, Complex.ext (by simp) (by simp [← h.2])⟩

lemma S180J_norm {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] {P : Matrix n n ℂ}
    (hP : P.PosSemidef) :
    ∃ r : Matrix n n ℂ, QAlgorithms.IsDensityMatrix r ∧ P = ((P.trace.re : ℝ) : ℂ) • r := by
  obtain ⟨h0, htr⟩ := S180J_tr_real hP
  generalize P.trace.re = a at h0 htr ⊢
  by_cases ha : a = 0
  · subst ha
    have hc : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
    refine ⟨((1 / (Fintype.card n : ℝ) : ℝ) : ℂ) • 1, ⟨?_, ?_⟩, ?_⟩
    · exact Matrix.PosSemidef.one.smul (by positivity)
    · rw [Matrix.trace_smul, Matrix.trace_one]; simp <;> field_simp
    · have : P.trace = 0 := by rw [htr]; simp
      rw [hP.trace_eq_zero_iff.mp this]; simp
  · have hpos : 0 < a := lt_of_le_of_ne h0 (Ne.symm ha)
    refine ⟨((a⁻¹ : ℝ) : ℂ) • P, ⟨hP.smul (by positivity), ?_⟩, ?_⟩
    · rw [Matrix.trace_smul, smul_eq_mul, htr, ← Complex.ofReal_mul, inv_mul_cancel₀ ha]; simp
    · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ha]; simp

open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P07 in
theorem solution {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    ∃ ap am : ℝ, ∃ rp rm : Matrix I I ℂ,
      JordanDecomposition A ap am rp rm ∧ traceNorm A = ap+am ∧ am = negativeMass A ∧
      ∀ bp bm sp sm, JordanDecomposition A bp bm sp sm → ap+am ≤ bp+bm := by
  set P := cfc (fun t : ℝ => max t 0) A with hPdef
  set Q := cfc (fun t : ℝ => max (-t) 0) A with hQdef
  have hP : P.PosSemidef := g53_cfc_psd A _ (fun t => le_max_right _ _)
  have hQ : Q.PosSemidef := g53_cfc_psd A _ (fun t => le_max_right _ _)
  obtain ⟨rp, hrp, hPr⟩ := S180J_norm hP
  obtain ⟨rm, hrm, hQr⟩ := S180J_norm hQ
  refine ⟨P.trace.re, Q.trace.re, rp, rm, ⟨(S180J_tr_real hP).1, (S180J_tr_real hQ).1, hrp, hrm,
    ?_⟩, g53_traceNorm_herm hA, ?_, ?_⟩
  · rw [← hPr, ← hQr]; exact (g53_parts A hA).symm
  · rw [hQdef, g53_cfc_trace hA, Complex.re_sum]
    simp only [Complex.ofReal_re]
    unfold negativeMass ascEigenvalues
    rw [dif_pos hA]
    rw [show (∑ k : Fin (Fintype.card I), max 0 (-hA.eigenvalues₀ (Fin.rev k))) =
        ∑ k : Fin (Fintype.card I), max 0 (-hA.eigenvalues₀ k) from
      Equiv.sum_comp Fin.revPerm (fun k => max 0 (-hA.eigenvalues₀ k))]
    rw [← Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [max_comm]; rfl
  · rintro bp bm sp sm ⟨hbp, hbm, hsp, hsm, hAe⟩
    have h1 : ((bp : ℂ) • sp).PosSemidef := hsp.1.smul (Complex.zero_le_real.mpr hbp)
    have h2 : ((bm : ℂ) • sm).PosSemidef := hsm.1.smul (Complex.zero_le_real.mpr hbm)
    have htri := g53_traceNorm_add_le h1.1 h2.1.neg
    rw [← sub_eq_add_neg, ← hAe, S180J_tn_neg, S180J_tn_psd h1, S180J_tn_psd h2,
      Matrix.trace_smul, Matrix.trace_smul, hsp.2, hsm.2] at htri
    rw [g53_traceNorm_herm hA] at htri
    simpa using htri
