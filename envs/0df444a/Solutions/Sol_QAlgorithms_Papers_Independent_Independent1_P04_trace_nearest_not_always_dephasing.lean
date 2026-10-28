-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P04.trace_nearest_not_always_dephasing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:44:35.189985+00:00
-- url     : https://prove2.me/submissions/3b35b9a6-82a3-4682-9e52-44f89b360adf

import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
set_option autoImplicit false
noncomputable section
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

lemma g53h_sqrt_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    cfc Real.sqrt A * cfc Real.sqrt A = A := by
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt A hA.nonneg]
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

lemma g53h_tr_psd_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  have hs : (cfc Real.sqrt A).IsHermitian := by
    have : (cfc Real.sqrt A).PosSemidef := by
      rw [← Matrix.nonneg_iff_posSemidef]; exact cfc_nonneg (fun x _ => Real.sqrt_nonneg x)
    exact this.1
  rw [← g53h_sqrt_sq hA, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h := hB.conjTranspose_mul_mul_same (cfc Real.sqrt A)
  rw [hs.eq] at h
  have := h.trace_nonneg
  rw [← Matrix.mul_assoc]
  exact (Complex.nonneg_iff.1 this).1

lemma g53h_tr_le_traceNorm {n : Type} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) (h1 : (1 - X).PosSemidef) (h2 : (1 + X).PosSemidef) :
    (X * Y).trace.re ≤ QAlgorithms.traceNorm Y := by
  rw [g53_traceNorm_herm hY]
  set P := cfc (fun t : ℝ => max t 0) Y
  set Q := cfc (fun t : ℝ => max (-t) 0) Y
  have hP : P.PosSemidef := g53_cfc_psd Y _ (fun t => le_max_right _ _)
  have hQ : Q.PosSemidef := g53_cfc_psd Y _ (fun t => le_max_right _ _)
  have hYPQ : Y = P - Q := (g53_parts Y hY).symm
  have a1 := g53h_tr_psd_mul h1 hP
  have a2 := g53h_tr_psd_mul h2 hQ
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at a1
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.trace_add, Complex.add_re] at a2
  rw [hYPQ, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  linarith


namespace S173L
open QAlgorithms

lemma psd_outer (r : Fin 3 → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    ((c : ℂ) • Matrix.vecMulVec (fun i => ((r i : ℝ) : ℂ)) (fun i => ((r i : ℝ) : ℂ))).PosSemidef := by
  have h := Matrix.posSemidef_vecMulVec_self_star (fun i => ((r i : ℝ) : ℂ))
  have e : star (fun i => ((r i : ℝ) : ℂ)) = (fun i => ((r i : ℝ) : ℂ)) := by
    funext i; simp [Complex.conj_ofReal]
  rw [e] at h
  have := h.smul (a := c) hc
  simpa [Complex.coe_smul] using this

lemma tn_psd {n : Type} [Fintype n] [DecidableEq n] {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    traceNorm P = P.trace.re := by
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

lemma tn_neg {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) :
    traceNorm (-P) = traceNorm P := by
  unfold traceNorm; simp [Matrix.conjTranspose_neg]

def psi : Fin 3 → ℝ := ![2/3, 1/3, 2/3]
def rho : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.vecMulVec (fun i => ((psi i : ℝ) : ℂ)) (fun i => ((psi i : ℝ) : ℂ))
def delta : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1/2, 0, 1/2]

lemma rho_psd : rho.PosSemidef := by
  have := psd_outer psi 1 zero_le_one
  simpa [rho] using this

lemma rho_trace : rho.trace = 1 := by
  simp [rho, psi, Matrix.trace, Fin.sum_univ_three, Matrix.vecMulVec_apply]; norm_num

lemma delta_inc : Papers.Independent.Independent1.P04.IncoherentState delta := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [delta, Matrix.posSemidef_diagonal_iff]
    intro i; fin_cases i <;> simp <;> norm_num
  · simp [delta, Matrix.trace_diagonal, Fin.sum_univ_three]; norm_num
  · intro i j hij; simp [delta, Matrix.diagonal_apply_ne _ hij]

-- lower bound
def u : Fin 3 → ℝ := ![3, 2, 3]
def av : Fin 3 → ℝ := ![1, 0, -1]
def bv : Fin 3 → ℝ := ![1, -3, 1]
def W : Matrix (Fin 3) (Fin 3) ℂ :=
  ((1/11 : ℝ) : ℂ) • Matrix.vecMulVec (fun i => ((u i : ℝ) : ℂ)) (fun i => ((u i : ℝ) : ℂ)) - 1

lemma W1 : (1 + W).PosSemidef := by
  have : 1 + W = ((1/11 : ℝ) : ℂ) • Matrix.vecMulVec (fun i => ((u i : ℝ) : ℂ)) (fun i => ((u i : ℝ) : ℂ)) := by
    simp [W]
  rw [this]; exact psd_outer u _ (by norm_num)

lemma W2 : (1 - W).PosSemidef := by
  have : 1 - W = ((1 : ℝ) : ℂ) • Matrix.vecMulVec (fun i => ((av i : ℝ) : ℂ)) (fun i => ((av i : ℝ) : ℂ)) +
      ((2/11 : ℝ) : ℂ) • Matrix.vecMulVec (fun i => ((bv i : ℝ) : ℂ)) (fun i => ((bv i : ℝ) : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [W, u, av, bv, Matrix.vecMulVec_apply, Matrix.one_apply] <;> norm_num
  rw [this]; exact (psd_outer av _ (by norm_num)).add (psd_outer bv _ (by norm_num))

lemma X_herm : (rho - Papers.Independent.Independent1.P04.dephasedMatrix rho).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rho, psi, Papers.Independent.Independent1.P04.dephasedMatrix, Matrix.vecMulVec_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply] <;> ring

lemma trWX : (W * (rho - Papers.Independent.Independent1.P04.dephasedMatrix rho)).trace.re = 40/33 := by
  simp [W, rho, psi, u, Papers.Independent.Independent1.P04.dephasedMatrix, Matrix.trace,
    Fin.sum_univ_three, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.one_apply,
    Matrix.diagonal_apply, Matrix.sub_apply]
  norm_num

-- upper bound
def w : Fin 3 → ℝ := ![7, 6, 7]
def l1 : Fin 3 → ℝ := ![1, -103/829, -1357/1658]
def l2 : Fin 3 → ℝ := ![0, 1, -103/76]
def l3 : Fin 3 → ℝ := ![0, 0, 1]
def P : Matrix (Fin 3) (Fin 3) ℂ :=
  ((3/670 : ℝ) : ℂ) • Matrix.vecMulVec (fun i => ((w i : ℝ) : ℂ)) (fun i => ((w i : ℝ) : ℂ))
def N : Matrix (Fin 3) (Fin 3) ℂ :=
  ((829/3015 : ℝ) : ℂ) • Matrix.vecMulVec (fun i => ((l1 i : ℝ) : ℂ)) (fun i => ((l1 i : ℝ) : ℂ)) +
  ((38/829 : ℝ) : ℂ) • Matrix.vecMulVec (fun i => ((l2 i : ℝ) : ℂ)) (fun i => ((l2 i : ℝ) : ℂ)) +
  ((1/152 : ℝ) : ℂ) • Matrix.vecMulVec (fun i => ((l3 i : ℝ) : ℂ)) (fun i => ((l3 i : ℝ) : ℂ))

lemma P_psd : P.PosSemidef := psd_outer w _ (by norm_num)
lemma N_psd : N.PosSemidef :=
  ((psd_outer l1 _ (by norm_num)).add (psd_outer l2 _ (by norm_num))).add (psd_outer l3 _ (by norm_num))

lemma Y_eq : rho - delta = P + -N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rho, psi, delta, P, N, w, l1, l2, l3, Matrix.vecMulVec_apply, Matrix.diagonal_apply] <;> norm_num

lemma trP : P.trace.re = 3/5 := by
  simp [P, w, Matrix.trace, Fin.sum_univ_three, Matrix.vecMulVec_apply]; norm_num
lemma trN : N.trace.re = 3/5 := by
  simp [N, l1, l2, l3, Matrix.trace, Fin.sum_univ_three, Matrix.vecMulVec_apply]; norm_num

end S173L

open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P04 S173L in
theorem solution :
    ∃ d : ℕ, 0 < d ∧ ∃ rho : CoherenceMatrix d, IsDensityMatrix rho ∧
      ∃ delta : CoherenceMatrix d, IncoherentState delta ∧
        fullTraceDistance d rho delta < fullTraceDistance d rho (dephasedMatrix rho) := by
  refine ⟨3, by norm_num, S173L.rho, ⟨rho_psd, rho_trace⟩, S173L.delta, delta_inc, ?_⟩
  unfold fullTraceDistance
  have hlow := g53h_tr_le_traceNorm X_herm W2 W1
  rw [trWX] at hlow
  have hup : traceNorm (S173L.rho - S173L.delta) ≤ 6/5 := by
    rw [Y_eq]
    have := g53_traceNorm_add_le P_psd.1 N_psd.1.neg
    rw [tn_neg, tn_psd P_psd, tn_psd N_psd, trP, trN] at this
    linarith
  linarith
