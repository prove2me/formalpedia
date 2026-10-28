-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P07.singlet_distance_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T16:46:51.595913+00:00
-- url     : https://prove2.me/submissions/ab0ae7f7-d551-4a2e-8d98-b44a2de69e77

import Definitions.Def_QAlgorithms_Defs_EntanglementNegativity
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P07_Model
set_option autoImplicit false


/-! Vidal–Werner, arXiv:quant-ph/0102117v1. All locators are PDF pages.
Paper-local operational and variational definitions precede their statements.
Deferred source inconsistencies and interfaces are recorded in HARD.md. -/

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P07

open Entanglement

end QAlgorithms.Papers.Independent.Independent1.P07

open scoped MatrixOrder

lemma p07s204_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma p07s204_conj_eig {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
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

lemma p07s204_posPart_aux {n : Type*} [Fintype n] [DecidableEq n] {A B U : Matrix n n ℂ} (lam : n → ℝ)
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

lemma p07s204_parts {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma p07s204_cfc_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma p07s204_posPart_le {n : Type*} [Fintype n] [DecidableEq n] {Y A B : Matrix n n ℂ} (hY : Y.IsHermitian)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hYAB : Y = A - B) :
    (cfc (fun t : ℝ => max t 0) Y).trace.re ≤ A.trace.re := by
  rw [p07s204_cfc_trace hY, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hD := p07s204_conj_eig hY
  have hu := Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize hY.eigenvalues = lam at *
  subst hYAB
  exact p07s204_posPart_aux lam hA hB hu hD

lemma p07s204_traceNorm_herm {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
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

lemma p07s204_negPart_eq {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc (fun t : ℝ => max (-t) 0) X = cfc (fun t : ℝ => max t 0) (-X) := by
  by_cases hX : IsSelfAdjoint X
  · exact cfc_comp_neg (f := fun t : ℝ => max t 0) (a := X)
  · have : ¬ IsSelfAdjoint (-X) := fun h => hX (by simpa using h.neg)
    rw [cfc_apply_of_not_predicate X hX, cfc_apply_of_not_predicate (-X) this]

/-- trace-norm triangle inequality for Hermitian matrices -/
lemma p07s204_traceNorm_add_le {n : Type*} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    QAlgorithms.traceNorm (X + Y) ≤ QAlgorithms.traceNorm X + QAlgorithms.traceNorm Y := by
  have hXY : (X + Y).IsHermitian := hX.add hY
  rw [p07s204_traceNorm_herm hXY, p07s204_traceNorm_herm hX, p07s204_traceNorm_herm hY]
  have pX := p07s204_cfc_psd X (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have mX := p07s204_cfc_psd X (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have pY := p07s204_cfc_psd Y (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have mY := p07s204_cfc_psd Y (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have eX := p07s204_parts X hX
  have eY := p07s204_parts Y hY
  have e1 : X + Y = (cfc (fun t : ℝ => max t 0) X + cfc (fun t : ℝ => max t 0) Y) -
      (cfc (fun t : ℝ => max (-t) 0) X + cfc (fun t : ℝ => max (-t) 0) Y) := by
    conv_lhs => rw [← eX, ← eY]
    abel
  have e2 : -(X + Y) = (cfc (fun t : ℝ => max (-t) 0) X + cfc (fun t : ℝ => max (-t) 0) Y) -
      (cfc (fun t : ℝ => max t 0) X + cfc (fun t : ℝ => max t 0) Y) := by
    rw [e1]; abel
  have h1 := p07s204_posPart_le hXY (pX.add pY) (mX.add mY) e1
  have h2 := p07s204_posPart_le hXY.neg (mX.add mY) (pX.add pY) e2
  rw [← p07s204_negPart_eq] at h2
  rw [Matrix.trace_add, Complex.add_re] at h1 h2
  linarith


lemma p07s204_tn_psd {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    QAlgorithms.traceNorm P = P.trace.re := by
  rw [p07s204_traceNorm_herm hP.1]
  have hsp : ∀ x ∈ spectrum ℝ P, 0 ≤ x := fun x hx =>
    spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hP) hx
  have e1 : cfc (fun t : ℝ => max t 0) P = P := by
    conv_rhs => rw [← cfc_id' ℝ P]
    exact cfc_congr fun x hx => max_eq_left (hsp x hx)
  have e2 : cfc (fun t : ℝ => max (-t) 0) P = 0 := by
    rw [← cfc_zero ℝ P]
    exact cfc_congr fun x hx => max_eq_right (by linarith [hsp x hx])
  rw [e1, e2]; simp

lemma p07s204_tn_neg {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) :
    QAlgorithms.traceNorm (-P) = QAlgorithms.traceNorm P := by
  unfold QAlgorithms.traceNorm; simp [Matrix.conjTranspose_neg]


lemma p07s204_sqrt_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    cfc Real.sqrt A * cfc Real.sqrt A = A := by
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt A hA.nonneg]
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

lemma p07s204_tr_psd_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  have hs : (cfc Real.sqrt A).IsHermitian := by
    have : (cfc Real.sqrt A).PosSemidef := by
      rw [← Matrix.nonneg_iff_posSemidef]; exact cfc_nonneg (fun x _ => Real.sqrt_nonneg x)
    exact this.1
  rw [← p07s204_sqrt_sq hA, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h := hB.conjTranspose_mul_mul_same (cfc Real.sqrt A)
  rw [hs.eq] at h
  have := h.trace_nonneg
  rw [← Matrix.mul_assoc]
  exact (Complex.nonneg_iff.1 this).1

lemma p07s204_tr_le_traceNorm {n : Type*} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) (h1 : (1 - X).PosSemidef) (h2 : (1 + X).PosSemidef) :
    (X * Y).trace.re ≤ QAlgorithms.traceNorm Y := by
  rw [p07s204_traceNorm_herm hY]
  set P := cfc (fun t : ℝ => max t 0) Y
  set Q := cfc (fun t : ℝ => max (-t) 0) Y
  have hP : P.PosSemidef := p07s204_cfc_psd Y _ (fun t => le_max_right _ _)
  have hQ : Q.PosSemidef := p07s204_cfc_psd Y _ (fun t => le_max_right _ _)
  have hYPQ : Y = P - Q := (p07s204_parts Y hY).symm
  have a1 := p07s204_tr_psd_mul h1 hP
  have a2 := p07s204_tr_psd_mul h2 hQ
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at a1
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.trace_add, Complex.add_re] at a2
  rw [hYPQ, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  linarith

lemma p07s204_proj_bound {I : Type*} [Fintype I] [DecidableEq I] {Y T : Matrix I I ℂ} (hY : Y.IsHermitian)
    (hT : T.IsHermitian) (hTT : T * T = T) :
    2 * (Y * T).trace.re ≤ Y.trace.re + QAlgorithms.traceNorm Y := by
  have hpT : T.PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self T
    rwa [hT.eq, hTT] at this
  have hpT' : (1 - T).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self (1 - T)
    have e : (1 - T)ᴴ * (1 - T) = 1 - T := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hT.eq, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hTT]; abel
    rwa [e] at this
  have h1 : (1 - ((2 : ℂ) • T - 1)).PosSemidef := by
    have : 1 - ((2 : ℂ) • T - 1) = (2 : ℂ) • (1 - T) := by rw [two_smul, two_smul]; abel
    rw [this]; exact hpT'.smul (by norm_num)
  have h2 : (1 + ((2 : ℂ) • T - 1)).PosSemidef := by
    have : 1 + ((2 : ℂ) • T - 1) = (2 : ℂ) • T := by abel
    rw [this]; exact hpT.smul (by norm_num)
  have k := p07s204_tr_le_traceNorm hY h1 h2
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re,
    Matrix.trace_mul_comm] at k
  simp at k
  linarith


lemma p07s204_tr_real {n : Type*} [Fintype n] {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    0 ≤ P.trace.re ∧ P.trace = ((P.trace.re : ℝ) : ℂ) := by
  have h := hP.trace_nonneg
  rw [Complex.nonneg_iff] at h
  refine ⟨h.1, Complex.ext (by simp) (by simp [← h.2])⟩

open QAlgorithms QAlgorithms.Entanglement QAlgorithms.Papers.Independent.Independent1.P07

lemma p07s204_tn_nonneg {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    0 ≤ traceNorm M := by
  unfold traceNorm
  exact (p07s204_tr_real (p07s204_cfc_psd (Mᴴ * M) Real.sqrt (fun t => Real.sqrt_nonneg t))).1

lemma p07s204_tn_zero {n : Type*} [Fintype n] [DecidableEq n] :
    traceNorm (0 : Matrix n n ℂ) = 0 := by
  simp [traceNorm, cfc_zero]

lemma p07s204_tn_sub_le {n : Type*} [Fintype n] [DecidableEq n] {P N : Matrix n n ℂ}
    (hP : P.PosSemidef) (hN : N.PosSemidef) :
    traceNorm (P - N) ≤ P.trace.re + N.trace.re := by
  have h := p07s204_traceNorm_add_le hP.1 hN.1.neg
  rwa [← sub_eq_add_neg, p07s204_tn_neg, p07s204_tn_psd hP, p07s204_tn_psd hN] at h

lemma p07s204_re_le_tn {n : Type*} [Fintype n] [DecidableEq n] {Z : Matrix n n ℂ}
    (hZ : Z.IsHermitian) : Z.trace.re ≤ traceNorm Z := by
  rw [p07s204_traceNorm_herm hZ]
  have hP := p07s204_cfc_psd Z (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have hN := p07s204_cfc_psd Z (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have e := p07s204_parts Z hZ
  have h2 := (p07s204_tr_real hN).1
  conv_lhs => rw [← e]
  rw [Matrix.trace_sub, Complex.sub_re]
  linarith

lemma p07s204_contract {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {o : ℕ} (Ψ : Fin o → Matrix n n ℂ → Matrix n' n' ℂ)
    (hlin : ∀ i X Y, Ψ i (X - Y) = Ψ i X - Ψ i Y)
    (hpsd : ∀ i X, X.PosSemidef → (Ψ i X).PosSemidef)
    (htr : ∀ X, ∑ i, (Ψ i X).trace = X.trace) (Z : Matrix n n ℂ) (hZ : Z.IsHermitian) :
    ∑ i, traceNorm (Ψ i Z) ≤ traceNorm Z := by
  set P := cfc (fun t : ℝ => max t 0) Z
  set N := cfc (fun t : ℝ => max (-t) 0) Z
  have hP : P.PosSemidef := p07s204_cfc_psd Z _ (fun t => le_max_right _ _)
  have hN : N.PosSemidef := p07s204_cfc_psd Z _ (fun t => le_max_right _ _)
  have hZe : Z = P - N := (p07s204_parts Z hZ).symm
  have hn := p07s204_traceNorm_herm hZ
  have h1 : ∀ i, traceNorm (Ψ i Z) ≤ (Ψ i P).trace.re + (Ψ i N).trace.re := fun i => by
    rw [hZe, hlin]; exact p07s204_tn_sub_le (hpsd i P hP) (hpsd i N hN)
  calc ∑ i, traceNorm (Ψ i Z) ≤ ∑ i, ((Ψ i P).trace.re + (Ψ i N).trace.re) :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = traceNorm Z := by
      rw [Finset.sum_add_distrib, ← Complex.re_sum, ← Complex.re_sum, htr, htr, hn]

section PT
variable {I J : Type*}

lemma p07s204_pt_herm {X : Matrix (I × J) (I × J) ℂ} (h : X.IsHermitian) :
    (partialTransposeFirst X).IsHermitian := by
  ext p q
  have := congrFun (congrFun h (q.1, p.2)) (p.1, q.2)
  simpa [partialTransposeFirst, Matrix.conjTranspose_apply] using this

lemma p07s204_pt_add (X Y : Matrix (I × J) (I × J) ℂ) :
    partialTransposeFirst (X + Y) = partialTransposeFirst X + partialTransposeFirst Y := by
  ext p q; simp [partialTransposeFirst]

lemma p07s204_pt_sub (X Y : Matrix (I × J) (I × J) ℂ) :
    partialTransposeFirst (X - Y) = partialTransposeFirst X - partialTransposeFirst Y := by
  ext p q; simp [partialTransposeFirst]

lemma p07s204_pt_zero : partialTransposeFirst (0 : Matrix (I × J) (I × J) ℂ) = 0 := by
  ext p q; simp [partialTransposeFirst]

lemma p07s204_pt_smul (c : ℂ) (X : Matrix (I × J) (I × J) ℂ) :
    partialTransposeFirst (c • X) = c • partialTransposeFirst X := by
  ext p q; simp [partialTransposeFirst]

lemma p07s204_pt_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (I × J) (I × J) ℂ) :
    partialTransposeFirst (∑ i ∈ s, f i) = ∑ i ∈ s, partialTransposeFirst (f i) := by
  ext p q; simp [partialTransposeFirst, Matrix.sum_apply]

lemma p07s204_pt_list_sum (L : List (Matrix (I × J) (I × J) ℂ)) :
    partialTransposeFirst L.sum = (L.map partialTransposeFirst).sum := by
  induction L with
  | nil => simp [p07s204_pt_zero]
  | cons x L ih => simp [p07s204_pt_add, ih]

lemma p07s204_trace_pt [Fintype I] [Fintype J] (X : Matrix (I × J) (I × J) ℂ) :
    (partialTransposeFirst X).trace = X.trace := by
  simp [Matrix.trace, partialTransposeFirst]

lemma p07s204_pt_alice {I' : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (K : Matrix I' I ℂ) (X : Matrix (I × J) (I × J) ℂ) :
    partialTransposeFirst (Matrix.kronecker K (1 : Matrix J J ℂ) * X *
        (Matrix.kronecker K (1 : Matrix J J ℂ))ᴴ) =
      Matrix.kronecker (K.map star) (1 : Matrix J J ℂ) * partialTransposeFirst X *
        (Matrix.kronecker (K.map star) (1 : Matrix J J ℂ))ᴴ := by
  ext ⟨x, y⟩ ⟨x', y'⟩
  simp [partialTransposeFirst, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kronecker, Matrix.one_apply, Fintype.sum_prod_type, apply_ite (starRingEnd ℂ), mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
  ring

lemma p07s204_pt_bob {J' : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (K : Matrix J' J ℂ) (X : Matrix (I × J) (I × J) ℂ) :
    partialTransposeFirst (Matrix.kronecker (1 : Matrix I I ℂ) K * X *
        (Matrix.kronecker (1 : Matrix I I ℂ) K)ᴴ) =
      Matrix.kronecker (1 : Matrix I I ℂ) K * partialTransposeFirst X *
        (Matrix.kronecker (1 : Matrix I I ℂ) K)ᴴ := by
  ext ⟨x, y⟩ ⟨x', y'⟩
  simp [partialTransposeFirst, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kronecker, Matrix.one_apply, Fintype.sum_prod_type, apply_ite (starRingEnd ℂ), mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

end PT

lemma p07s204_kraus_psd {K n n' : Type*} [Fintype K] [Fintype n] [Fintype n']
    (E : K → Matrix n' n ℂ) {X : Matrix n n ℂ} (hX : X.PosSemidef) : (krausApply E X).PosSemidef :=
  Matrix.posSemidef_sum _ fun j _ => hX.mul_mul_conjTranspose_same (E j)

lemma p07s204_kraus_sub {K n n' : Type*} [Fintype K] [Fintype n]
    (E : K → Matrix n' n ℂ) (X Y : Matrix n n ℂ) :
    krausApply E (X - Y) = krausApply E X - krausApply E Y := by
  simp [krausApply, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

lemma p07s204_pt_kraus_alice {I I' J K : Type*} [Fintype I] [Fintype J] [DecidableEq J] [Fintype K]
    (E : K → Matrix I' I ℂ) (X : Matrix (I × J) (I × J) ℂ) :
    partialTransposeFirst (krausApply (fun j => Matrix.kronecker (E j) (1 : Matrix J J ℂ)) X) =
      krausApply (fun j => Matrix.kronecker ((E j).map star) (1 : Matrix J J ℂ))
        (partialTransposeFirst X) := by
  simp only [krausApply, p07s204_pt_sum, p07s204_pt_alice]

lemma p07s204_pt_kraus_bob {I J J' K : Type*} [Fintype I] [Fintype J] [DecidableEq I] [Fintype K]
    (E : K → Matrix J' J ℂ) (X : Matrix (I × J) (I × J) ℂ) :
    partialTransposeFirst (krausApply (fun j => Matrix.kronecker (1 : Matrix I I ℂ) (E j)) X) =
      krausApply (fun j => Matrix.kronecker (1 : Matrix I I ℂ) (E j)) (partialTransposeFirst X) := by
  simp only [krausApply, p07s204_pt_sum, p07s204_pt_bob]

lemma p07s204_kron_sum_left {ι A B J : Type*} [DecidableEq J] (s : Finset ι) (f : ι → Matrix A B ℂ) :
    Matrix.kronecker (∑ i ∈ s, f i) (1 : Matrix J J ℂ) = ∑ i ∈ s, Matrix.kronecker (f i) 1 := by
  ext p q; simp [Matrix.kronecker, Matrix.sum_apply, Finset.sum_mul]

lemma p07s204_kron_sum_right {ι A B I : Type*} [DecidableEq I] (s : Finset ι) (f : ι → Matrix A B ℂ) :
    Matrix.kronecker (1 : Matrix I I ℂ) (∑ i ∈ s, f i) = ∑ i ∈ s, Matrix.kronecker 1 (f i) := by
  ext p q; simp [Matrix.kronecker, Matrix.sum_apply, Finset.mul_sum]

lemma p07s204_trace_alice {a c o : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (M : LocalInstrument a c o) (X : Matrix (Fin a × J) (Fin a × J) ℂ) :
    ∑ i, (krausApply (fun j => Matrix.kronecker (M.kraus i j) (1 : Matrix J J ℂ)) X).trace =
      X.trace := by
  have h : ∀ i j, (Matrix.kronecker (M.kraus i j) (1 : Matrix J J ℂ) * X *
      (Matrix.kronecker (M.kraus i j) (1 : Matrix J J ℂ))ᴴ).trace =
      (Matrix.kronecker ((M.kraus i j)ᴴ * M.kraus i j) (1 : Matrix J J ℂ) * X).trace := by
    intro i j
    rw [Matrix.trace_mul_cycle]
    congr 2
    simp only [Matrix.kronecker]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul]
  calc ∑ i, (krausApply (fun j => Matrix.kronecker (M.kraus i j) (1 : Matrix J J ℂ)) X).trace
      = ∑ i, ∑ j, (Matrix.kronecker ((M.kraus i j)ᴴ * M.kraus i j) (1 : Matrix J J ℂ) * X).trace := by
        simp only [krausApply, Matrix.trace_sum, h]
    _ = (Matrix.kronecker (∑ i, ∑ j, (M.kraus i j)ᴴ * M.kraus i j) (1 : Matrix J J ℂ) * X).trace := by
        simp only [p07s204_kron_sum_left, Finset.sum_mul, Matrix.trace_sum]
    _ = X.trace := by
        rw [M.complete]; simp only [Matrix.kronecker, Matrix.one_kronecker_one, Matrix.one_mul]

lemma p07s204_trace_bob {b d o : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : LocalInstrument b d o) (X : Matrix (I × Fin b) (I × Fin b) ℂ) :
    ∑ i, (krausApply (fun j => Matrix.kronecker (1 : Matrix I I ℂ) (M.kraus i j)) X).trace =
      X.trace := by
  have h : ∀ i j, (Matrix.kronecker (1 : Matrix I I ℂ) (M.kraus i j) * X *
      (Matrix.kronecker (1 : Matrix I I ℂ) (M.kraus i j))ᴴ).trace =
      (Matrix.kronecker (1 : Matrix I I ℂ) ((M.kraus i j)ᴴ * M.kraus i j) * X).trace := by
    intro i j
    rw [Matrix.trace_mul_cycle]
    congr 2
    simp only [Matrix.kronecker]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul]
  calc ∑ i, (krausApply (fun j => Matrix.kronecker (1 : Matrix I I ℂ) (M.kraus i j)) X).trace
      = ∑ i, ∑ j, (Matrix.kronecker (1 : Matrix I I ℂ) ((M.kraus i j)ᴴ * M.kraus i j) * X).trace := by
        simp only [krausApply, Matrix.trace_sum, h]
    _ = (Matrix.kronecker (1 : Matrix I I ℂ) (∑ i, ∑ j, (M.kraus i j)ᴴ * M.kraus i j) * X).trace := by
        simp only [p07s204_kron_sum_right, Finset.sum_mul, Matrix.trace_sum]
    _ = X.trace := by
        rw [M.complete]; simp only [Matrix.kronecker, Matrix.one_kronecker_one, Matrix.one_mul]

lemma p07s204_flat {α β γ : Type*} [AddCommMonoid γ] (l : List α) (f : α → List β) (g : β → γ) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem p07s204_tree {a b c d : ℕ} (P : Protocol a b c d) :
    ∀ rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ, rho.PosSemidef →
      ((protocolBranches P rho).map fun X => traceNorm (partialTransposeFirst X)).sum ≤
          traceNorm (partialTransposeFirst rho) ∧
        ((protocolBranches P rho).map Matrix.trace).sum = rho.trace ∧
        ∀ X ∈ protocolBranches P rho, X.PosSemidef := by
  induction P with
  | finish a b => intro rho h; simp [protocolBranches, h]
  | @alice a b c d aNext o hpos M next ih =>
    intro rho h
    have hb : ∀ i, (krausApply (fun j => Matrix.kronecker (M.kraus i j)
        (1 : Matrix (Fin b) (Fin b) ℂ)) rho).PosSemidef := fun i => p07s204_kraus_psd _ h
    refine ⟨?_, ?_, ?_⟩
    · simp only [protocolBranches, p07s204_flat, ← Fin.sum_univ_def]
      calc _ ≤ ∑ i, traceNorm (partialTransposeFirst (krausApply (fun j => Matrix.kronecker
              (M.kraus i j) (1 : Matrix (Fin b) (Fin b) ℂ)) rho)) :=
            Finset.sum_le_sum fun i _ => (ih i _ (hb i)).1
        _ ≤ _ := by
          simp only [p07s204_pt_kraus_alice]
          refine p07s204_contract _ (fun i X Y => p07s204_kraus_sub _ X Y)
            (fun i X hX => p07s204_kraus_psd _ hX) (fun X => ?_) _ (p07s204_pt_herm h.1)
          rw [← p07s204_trace_pt X, ← p07s204_trace_alice M (partialTransposeFirst X)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← p07s204_trace_pt, p07s204_pt_kraus_alice]
          congr 3
          funext j
          congr 1
          ext; simp
    · simp only [protocolBranches, p07s204_flat, ← Fin.sum_univ_def]
      rw [Finset.sum_congr rfl fun i _ => (ih i _ (hb i)).2.1]
      exact p07s204_trace_alice M rho
    · intro X hX
      simp only [protocolBranches, List.mem_flatMap] at hX
      obtain ⟨i, _, hi⟩ := hX
      exact (ih i _ (hb i)).2.2 X hi
  | @bob a b c d bNext o hpos M next ih =>
    intro rho h
    have hb : ∀ i, (krausApply (fun j => Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ)
        (M.kraus i j)) rho).PosSemidef := fun i => p07s204_kraus_psd _ h
    refine ⟨?_, ?_, ?_⟩
    · simp only [protocolBranches, p07s204_flat, ← Fin.sum_univ_def]
      calc _ ≤ ∑ i, traceNorm (partialTransposeFirst (krausApply (fun j => Matrix.kronecker
              (1 : Matrix (Fin a) (Fin a) ℂ) (M.kraus i j)) rho)) :=
            Finset.sum_le_sum fun i _ => (ih i _ (hb i)).1
        _ ≤ _ := by
          simp only [p07s204_pt_kraus_bob]
          refine p07s204_contract _ (fun i X Y => p07s204_kraus_sub _ X Y)
            (fun i X hX => p07s204_kraus_psd _ hX) (fun X => ?_) _ (p07s204_pt_herm h.1)
          rw [← p07s204_trace_pt X, ← p07s204_trace_bob M (partialTransposeFirst X)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← p07s204_trace_pt, p07s204_pt_kraus_bob]
    · simp only [protocolBranches, p07s204_flat, ← Fin.sum_univ_def]
      rw [Finset.sum_congr rfl fun i _ => (ih i _ (hb i)).2.1]
      exact p07s204_trace_bob M rho
    · intro X hX
      simp only [protocolBranches, List.mem_flatMap] at hX
      obtain ⟨i, _, hi⟩ := hX
      exact (ih i _ (hb i)).2.2 X hi

lemma p07s204_tn_list_sum {n : Type*} [Fintype n] [DecidableEq n] (L : List (Matrix n n ℂ))
    (h : ∀ X ∈ L, X.IsHermitian) :
    traceNorm L.sum ≤ (L.map traceNorm).sum ∧ L.sum.IsHermitian := by
  induction L with
  | nil => simp [p07s204_tn_zero]
  | cons x L ih =>
    obtain ⟨ih1, ih2⟩ := ih fun X hX => h X (by simp [hX])
    have hx := h x (by simp)
    refine ⟨?_, by simpa using hx.add ih2⟩
    simp only [List.sum_cons, List.map_cons]
    have := p07s204_traceNorm_add_le hx ih2
    linarith

lemma p07s204_output {a b c d : ℕ} (P : Protocol a b c d)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hrho : IsDensityMatrix rho) :
    traceNorm (partialTransposeFirst (protocolOutput P rho)) ≤
        traceNorm (partialTransposeFirst rho) ∧
      (protocolOutput P rho).IsHermitian ∧ (protocolOutput P rho).trace = 1 := by
  obtain ⟨hT, htr, hpsd⟩ := p07s204_tree P rho hrho.1
  have hL := p07s204_tn_list_sum ((protocolBranches P rho).map partialTransposeFirst)
    (fun X hX => by
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
      exact p07s204_pt_herm (hpsd Y hY).1)
  rw [List.map_map] at hL
  refine ⟨?_, (p07s204_tn_list_sum _ fun X hX => (hpsd X hX).1).2, ?_⟩
  · rw [protocolOutput, p07s204_pt_list_sum]
    exact hL.1.trans hT
  · rw [protocolOutput, Matrix.trace_list_sum, htr, hrho.2]

lemma p07s204_singlet_apply (m : ℕ) (hm : 0 < m) (p q : Fin m × Fin m) :
    singlet m hm p q = if p.1 = p.2 ∧ q.1 = q.2 then ((m : ℂ))⁻¹ else 0 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have e : ((Real.sqrt m : ℂ))⁻¹ * (starRingEnd ℂ) ((Real.sqrt m : ℂ))⁻¹ = ((m : ℂ))⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hm'.le]
    simp
  simp only [singlet, pureDensity, finiteMaxEntangled, Matrix.of_apply, Fintype.card_fin]
  split_ifs with h1 h2 h3 <;> simp_all

lemma p07s204_singlet_herm (m : ℕ) (hm : 0 < m) : (singlet m hm).IsHermitian := by
  ext p q
  simp only [Matrix.conjTranspose_apply, p07s204_singlet_apply]
  by_cases h : p.1 = p.2 ∧ q.1 = q.2
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]; simp
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩)]; simp

lemma p07s204_singlet_trace (m : ℕ) (hm : 0 < m) : (singlet m hm).trace = 1 := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  simp [Matrix.trace, p07s204_singlet_apply, Fintype.sum_prod_type, hm']

lemma p07s204_singlet_sq (m : ℕ) (hm : 0 < m) : singlet m hm * singlet m hm = singlet m hm := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  ext p q
  simp only [Matrix.mul_apply, p07s204_singlet_apply, Fintype.sum_prod_type]
  by_cases h1 : p.1 = p.2 <;> by_cases h2 : q.1 = q.2 <;>
    simp [h1, h2, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', hm']

lemma p07s204_singlet_pt (m : ℕ) (hm : 0 < m) :
    partialTransposeFirst (singlet m hm) = ((m : ℂ))⁻¹ • swapOp := by
  ext p q
  simp only [partialTransposeFirst, Matrix.of_apply, p07s204_singlet_apply, swapOp,
    Matrix.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  congr 1
  apply propext
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2.symm, h1⟩

lemma p07s204_trace_pt_mul {I J : Type*} [Fintype I] [Fintype J]
    (A B : Matrix (I × J) (I × J) ℂ) :
    (partialTransposeFirst A * partialTransposeFirst B).trace = (A * B).trace := by
  let e : (I × J) × (I × J) ≃ (I × J) × (I × J) :=
    { toFun := fun x => ((x.2.1, x.1.2), (x.1.1, x.2.2))
      invFun := fun x => ((x.2.1, x.1.2), (x.1.1, x.2.2))
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv e _ _ (fun x => rfl)

lemma p07s204_involution_psd {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) (hXX : X * X = 1) : (1 - X).PosSemidef ∧ (1 + X).PosSemidef := by
  have h1 := Matrix.posSemidef_conjTranspose_mul_self (1 - X)
  have h2 := Matrix.posSemidef_conjTranspose_mul_self (1 + X)
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hX.eq] at h1
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hX.eq] at h2
  have e1 : (1 - X) * (1 - X) = (2 : ℂ) • (1 - X) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hXX, two_smul]; simp; abel
  have e2 : (1 + X) * (1 + X) = (2 : ℂ) • (1 + X) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hXX, two_smul]; simp; abel
  rw [e1] at h1; rw [e2] at h2
  have hh : (0 : ℂ) ≤ 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.zero_le_real.mpr (by norm_num)
  have k1 := h1.smul hh
  have k2 := h2.smul hh
  rw [smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul] at k1 k2
  exact ⟨k1, k2⟩

lemma p07s204_swap_herm (m : ℕ) : (swapOp : Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ).IsHermitian := by
  ext p q
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  simp only [Matrix.conjTranspose_apply, swapOp, Matrix.of_apply, Prod.mk.injEq]
  by_cases h : q1 = p2 ∧ q2 = p1
  · rw [if_pos h, if_pos ⟨h.2.symm, h.1.symm⟩]; simp
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2.symm, h'.1.symm⟩)]; simp

lemma p07s204_swap_sq (m : ℕ) :
    (swapOp : Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ) * swapOp = 1 := by
  ext p q
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  simp only [Matrix.mul_apply, swapOp, Matrix.of_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Prod.mk.injEq, mul_ite, mul_one, mul_zero, ite_and]
  by_cases h1 : p1 = q1 <;> by_cases h2 : p2 = q2 <;>
    simp [h1, h2, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]

lemma p07s204_bound {m : ℕ} (hm : 0 < m) (sigma : Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ)
    (hs : sigma.IsHermitian) (htr : sigma.trace = 1) :
    2 * (1 - traceNorm (partialTransposeFirst sigma) / (m : ℝ)) ≤
      traceNorm (singlet m hm - sigma) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set S := singlet m hm
  have hS := p07s204_singlet_herm m hm
  -- step (i)
  have k := p07s204_proj_bound (hS.sub hs) hS (p07s204_singlet_sq m hm)
  rw [Matrix.sub_mul, p07s204_singlet_sq m hm, Matrix.trace_sub, Matrix.trace_sub,
    p07s204_singlet_trace, htr, Matrix.trace_mul_comm sigma S] at k
  simp only [sub_self, Complex.zero_re, Complex.sub_re, Complex.one_re] at k
  -- step (ii)
  have hF := p07s204_involution_psd (p07s204_swap_herm m) (p07s204_swap_sq m)
  have k2 := p07s204_tr_le_traceNorm (p07s204_pt_herm hs) hF.1 hF.2
  have e : (S * sigma).trace.re = ((m : ℝ))⁻¹ *
      (swapOp * partialTransposeFirst sigma).trace.re := by
    rw [← p07s204_trace_pt_mul, p07s204_singlet_pt, Matrix.smul_mul, Matrix.trace_smul,
      smul_eq_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  have k3 : (S * sigma).trace.re ≤ traceNorm (partialTransposeFirst sigma) / m := by
    rw [e, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right k2 hm'.le
  linarith

open QAlgorithms QAlgorithms.Entanglement QAlgorithms.Papers.Independent.Independent1.P07 in
theorem solution {m : ℕ} (hm : 0 < m)
    (rho : Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ) (hrho : IsDensityMatrix rho) :
    2*(1-(1+2*negativity rho)/(m : ℝ)) ≤ singletDistance m hm rho := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN : 1 + 2 * negativity rho = traceNorm (partialTransposeFirst rho) := by
    rw [negativity]; ring
  rw [hN]
  rw [singletDistance]
  refine le_csInf ⟨_, Protocol.finish m m, rfl⟩ ?_
  rintro v ⟨P, rfl⟩
  obtain ⟨hle, hs, htr⟩ := p07s204_output P rho hrho
  refine le_trans ?_ (p07s204_bound hm _ hs htr)
  have : traceNorm (partialTransposeFirst (protocolOutput P rho)) / (m : ℝ) ≤
      traceNorm (partialTransposeFirst rho) / m := div_le_div_of_nonneg_right hle hm'.le
  linarith
