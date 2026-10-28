-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P07.multipartite_monotones
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T17:01:24.939052+00:00
-- url     : https://prove2.me/submissions/389aaaf0-bd40-4e98-af4d-f3279a0abd26

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

lemma p07s204_tn_smul {n : Type*} [Fintype n] [DecidableEq n] (r : ℝ) (hr : 0 ≤ r)
    (M : Matrix n n ℂ) : traceNorm ((r : ℂ) • M) = r * traceNorm M := by
  unfold traceNorm
  have e : ((r : ℂ) • M)ᴴ * ((r : ℂ) • M) = (r ^ 2 : ℝ) • (Mᴴ * M) := by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show star (r : ℂ) * (r : ℂ) = ((r ^ 2 : ℝ) : ℂ) by simp [sq]]
    rw [Complex.coe_smul]
  have hsa : IsSelfAdjoint (Mᴴ * M) := (Matrix.isHermitian_conjTranspose_mul_self M).isSelfAdjoint
  rw [e, ← cfc_comp_smul (r ^ 2) Real.sqrt (Mᴴ * M)]
  have e2 : (fun x : ℝ => Real.sqrt ((r ^ 2) • x)) = fun x => r * Real.sqrt x := by
    funext x
    rw [smul_eq_mul, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]
  rw [e2, cfc_const_mul r Real.sqrt (Mᴴ * M), Matrix.trace_smul]
  simp

lemma p07s204_avg_le {c d : ℕ} (X : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ) :
    (if 0 < X.trace.re then X.trace.re * negativity ((X.trace.re : ℂ)⁻¹ • X) else 0) ≤
      (traceNorm (partialTransposeFirst X) - X.trace.re) / 2 := by
  split_ifs with h
  · rw [negativity, p07s204_pt_smul, ← Complex.ofReal_inv,
      p07s204_tn_smul _ (inv_nonneg.2 h.le)]
    field_simp
    ring_nf
    rfl
  · have := p07s204_tn_nonneg (partialTransposeFirst X); linarith

lemma p07s204_tn_finset_sum {ι n : Type*} [Fintype n] [DecidableEq n] (s : Finset ι)
    (f : ι → Matrix n n ℂ) (hf : ∀ i ∈ s, (f i).IsHermitian) :
    traceNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, traceNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [p07s204_tn_zero]
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    have hs : (∑ i ∈ s, f i).IsHermitian := by
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_sum]
      exact Finset.sum_congr rfl fun i hi => hf i (by simp [hi])
    have := p07s204_traceNorm_add_le (hf x (by simp)) hs
    have := ih fun i hi => hf i (by simp [hi])
    linarith

lemma p07s204_sum_get {α γ : Type*} [AddCommMonoid γ] (B : List α) (g : α → γ) :
    ∑ j : Fin B.length, g (B.get j) = (B.map g).sum := by
  rw [← List.sum_ofFn]
  conv_rhs => rw [← List.ofFn_get B, List.map_ofFn]
  rfl


lemma p07s204_submatrix_sum {ι N M : Type*} (s : Finset ι) (F : ι → Matrix N N ℂ) (f : M → N) :
    (∑ i ∈ s, F i).submatrix f f = ∑ i ∈ s, (F i).submatrix f f := by
  ext p q; simp [Matrix.sum_apply]

lemma p07s204_kraus_regroup {N N' M M' K : Type*} [Fintype N] [Fintype N'] [Fintype M] [Fintype M']
    [Fintype K] (f : M ≃ N) (f' : M' ≃ N') (E : K → Matrix N' N ℂ) (X : Matrix N N ℂ) :
    (krausApply E X).submatrix f' f' =
      krausApply (fun j => (E j).submatrix f' f) (X.submatrix f f) := by
  simp only [krausApply, p07s204_submatrix_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

lemma p07s204_pt_prod {G G' H H' : Type*} [Fintype G] [Fintype H] [Fintype H'] [DecidableEq G]
    [DecidableEq H'] (A : Matrix G' G ℂ) (B : Matrix H' H ℂ) (X : Matrix (G × H) (G × H) ℂ) :
    partialTransposeFirst (Matrix.kronecker A B * X * (Matrix.kronecker A B)ᴴ) =
      Matrix.kronecker (A.map star) B * partialTransposeFirst X *
        (Matrix.kronecker (A.map star) B)ᴴ := by
  have hk : ∀ A' : Matrix G' G ℂ, Matrix.kronecker A' B =
      Matrix.kronecker A' (1 : Matrix H' H' ℂ) * Matrix.kronecker (1 : Matrix G G ℂ) B := by
    intro A'
    simp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hk A, hk (A.map star), Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have e : ∀ (P : Matrix (G' × H') (G × H') ℂ) (Q : Matrix (G × H') (G × H) ℂ)
      (Y : Matrix (G × H) (G × H) ℂ), P * Q * Y * (Qᴴ * Pᴴ) = P * (Q * Y * Qᴴ) * Pᴴ := by
    intro P Q Y; simp only [Matrix.mul_assoc]
  rw [e, e, p07s204_pt_alice, p07s204_pt_bob]

lemma p07s204_trace_kraus {N N' : Type*} [Fintype N] [Fintype N'] [DecidableEq N] {o : ℕ}
    (mult : Fin o → ℕ) (E : (i : Fin o) → Fin (mult i) → Matrix N' N ℂ)
    (h : ∑ i, ∑ j, (E i j)ᴴ * E i j = 1) (X : Matrix N N ℂ) :
    ∑ i, (krausApply (E i) X).trace = X.trace := by
  calc ∑ i, (krausApply (E i) X).trace = ∑ i, ∑ j, ((E i j)ᴴ * E i j * X).trace := by
        simp only [krausApply, Matrix.trace_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.trace_mul_cycle]
    _ = ((∑ i, ∑ j, (E i j)ᴴ * E i j) * X).trace := by
        simp only [Finset.sum_mul, Matrix.trace_sum]
    _ = X.trace := by rw [h, Matrix.one_mul]

lemma p07s204_step {N N' G H G' H' : Type*} [Fintype N] [Fintype N'] [DecidableEq N]
    [DecidableEq N'] [Fintype G] [Fintype H] [Fintype G'] [Fintype H'] [DecidableEq G]
    [DecidableEq H] [DecidableEq G'] [DecidableEq H']
    (f : G × H ≃ N) (f' : G' × H' ≃ N') {o : ℕ} (mult : Fin o → ℕ)
    (E : (i : Fin o) → Fin (mult i) → Matrix N' N ℂ) (hcomp : ∑ i, ∑ j, (E i j)ᴴ * E i j = 1)
    (A : (i : Fin o) → Fin (mult i) → Matrix G' G ℂ) (B : (i : Fin o) → Fin (mult i) → Matrix H' H ℂ)
    (hprod : ∀ i j, (E i j).submatrix f' f = Matrix.kronecker (A i j) (B i j))
    (rho : Matrix N N ℂ) (hrho : rho.PosSemidef) :
    ∑ i, traceNorm (partialTransposeFirst ((krausApply (E i) rho).submatrix f' f')) ≤
      traceNorm (partialTransposeFirst (rho.submatrix f f)) := by
  have e1 : ∀ i (Y : Matrix N N ℂ), partialTransposeFirst ((krausApply (E i) Y).submatrix f' f') =
      krausApply (fun j => Matrix.kronecker ((A i j).map star) (B i j))
        (partialTransposeFirst (Y.submatrix f f)) := by
    intro i Y
    rw [p07s204_kraus_regroup f f']
    simp only [hprod, krausApply, p07s204_pt_sum, p07s204_pt_prod]
  have hcomp' : ∑ i, ∑ j, ((E i j).submatrix f' f)ᴴ * (E i j).submatrix f' f = 1 := by
    have : ∀ i j, ((E i j).submatrix f' f)ᴴ * (E i j).submatrix f' f =
        ((E i j)ᴴ * E i j).submatrix f f := by
      intro i j; rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    simp only [this, ← p07s204_submatrix_sum, hcomp, Matrix.submatrix_one_equiv]
  simp only [e1]
  refine p07s204_contract _ (fun i X Y => p07s204_kraus_sub _ X Y)
    (fun i X hX => p07s204_kraus_psd _ hX) (fun Y => ?_) _
    (p07s204_pt_herm (hrho.submatrix f).1)
  have e2 : ∀ i, krausApply (fun j => Matrix.kronecker ((A i j).map star) (B i j)) Y =
      partialTransposeFirst (krausApply (fun j => (E i j).submatrix f' f)
        (partialTransposeFirst Y)) := by
    intro i
    simp only [hprod, krausApply, p07s204_pt_sum, p07s204_pt_prod]
    rfl
  simp only [e2, p07s204_trace_pt]
  rw [p07s204_trace_kraus mult _ hcomp', p07s204_trace_pt]

lemma p07s204_comp_left {I I' J : Type*} [Fintype I] [Fintype I'] [DecidableEq I] [Fintype J]
    [DecidableEq J] {o : ℕ} (mult : Fin o → ℕ) (K : (i : Fin o) → Fin (mult i) → Matrix I' I ℂ)
    (h : ∑ i, ∑ j, (K i j)ᴴ * K i j = 1) :
    ∑ i, ∑ j, (Matrix.kronecker (K i j) (1 : Matrix J J ℂ))ᴴ *
      Matrix.kronecker (K i j) (1 : Matrix J J ℂ) = 1 := by
  have e : ∀ i j, (Matrix.kronecker (K i j) (1 : Matrix J J ℂ))ᴴ *
      Matrix.kronecker (K i j) (1 : Matrix J J ℂ) =
      Matrix.kronecker ((K i j)ᴴ * K i j) (1 : Matrix J J ℂ) := by
    intro i j; simp only [Matrix.kronecker]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul]
  simp only [e, ← p07s204_kron_sum_left, h]
  simp only [Matrix.kronecker, Matrix.one_kronecker_one]

lemma p07s204_comp_right {I J J' : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype J']
    [DecidableEq J] {o : ℕ} (mult : Fin o → ℕ) (K : (i : Fin o) → Fin (mult i) → Matrix J' J ℂ)
    (h : ∑ i, ∑ j, (K i j)ᴴ * K i j = 1) :
    ∑ i, ∑ j, (Matrix.kronecker (1 : Matrix I I ℂ) (K i j))ᴴ *
      Matrix.kronecker (1 : Matrix I I ℂ) (K i j) = 1 := by
  have e : ∀ i j, (Matrix.kronecker (1 : Matrix I I ℂ) (K i j))ᴴ *
      Matrix.kronecker (1 : Matrix I I ℂ) (K i j) =
      Matrix.kronecker (1 : Matrix I I ℂ) ((K i j)ᴴ * K i j) := by
    intro i j; simp only [Matrix.kronecker]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul]
  simp only [e, ← p07s204_kron_sum_right, h]
  simp only [Matrix.kronecker, Matrix.one_kronecker_one]

theorem p07s204_tree3 (G H : ℕ → ℕ → ℕ → Type) [∀ a b c, Fintype (G a b c)]
    [∀ a b c, DecidableEq (G a b c)] [∀ a b c, Fintype (H a b c)] [∀ a b c, DecidableEq (H a b c)]
    (f : ∀ a b c, G a b c × H a b c ≃ Fin a × (Fin b × Fin c))
    (hA : ∀ a a' b c (K : Matrix (Fin a') (Fin a) ℂ), ∃ A : Matrix (G a' b c) (G a b c) ℂ,
      ∃ B : Matrix (H a' b c) (H a b c) ℂ,
      (Matrix.kronecker K (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ)).submatrix (f a' b c)
        (f a b c) = Matrix.kronecker A B)
    (hB : ∀ a b b' c (K : Matrix (Fin b') (Fin b) ℂ), ∃ A : Matrix (G a b' c) (G a b c) ℂ,
      ∃ B : Matrix (H a b' c) (H a b c) ℂ,
      (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ)
        (Matrix.kronecker K (1 : Matrix (Fin c) (Fin c) ℂ))).submatrix (f a b' c) (f a b c) =
        Matrix.kronecker A B)
    (hC : ∀ a b c c' (K : Matrix (Fin c') (Fin c) ℂ), ∃ A : Matrix (G a b c') (G a b c) ℂ,
      ∃ B : Matrix (H a b c') (H a b c) ℂ,
      (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ)
        (Matrix.kronecker (1 : Matrix (Fin b) (Fin b) ℂ) K)).submatrix (f a b c') (f a b c) =
        Matrix.kronecker A B)
    {a b c x y z : ℕ} (P : ThreePartyProtocol a b c x y z) :
    ∀ rho : Matrix (Fin a × (Fin b × Fin c)) (Fin a × (Fin b × Fin c)) ℂ, rho.PosSemidef →
      ((threePartyBranches P rho).map fun X =>
          traceNorm (partialTransposeFirst (X.submatrix (f x y z) (f x y z)))).sum ≤
          traceNorm (partialTransposeFirst (rho.submatrix (f a b c) (f a b c))) ∧
        ((threePartyBranches P rho).map Matrix.trace).sum = rho.trace ∧
        ∀ X ∈ threePartyBranches P rho, X.PosSemidef := by
  induction P with
  | finish a b c => intro rho h; simp [threePartyBranches, h]
  | @alice a b c x y z aNext o hpos M next ih =>
    intro rho h
    let E := fun i j => Matrix.kronecker (M.kraus i j)
      (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ)
    have hcomp : ∑ i, ∑ j, (E i j)ᴴ * E i j = 1 := p07s204_comp_left _ _ M.complete
    choose A B hAB using fun i j => hA a aNext b c (M.kraus i j)
    have hb : ∀ i, (krausApply (E i) rho).PosSemidef := fun i => p07s204_kraus_psd _ h
    refine ⟨?_, ?_, ?_⟩
    · simp only [threePartyBranches, p07s204_flat, ← Fin.sum_univ_def]
      exact (Finset.sum_le_sum fun i _ => (ih i _ (hb i)).1).trans
        (p07s204_step (f a b c) (f aNext b c) M.multiplicity E hcomp A B hAB rho h)
    · simp only [threePartyBranches, p07s204_flat, ← Fin.sum_univ_def]
      rw [Finset.sum_congr rfl fun i _ => (ih i _ (hb i)).2.1]
      exact p07s204_trace_kraus _ E hcomp rho
    · intro X hX
      simp only [threePartyBranches, List.mem_flatMap] at hX
      obtain ⟨i, _, hi⟩ := hX
      exact (ih i _ (hb i)).2.2 X hi
  | @bob a b c x y z bNext o hpos M next ih =>
    intro rho h
    let E := fun i j => Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ)
      (Matrix.kronecker (M.kraus i j) (1 : Matrix (Fin c) (Fin c) ℂ))
    have hcomp : ∑ i, ∑ j, (E i j)ᴴ * E i j = 1 :=
      p07s204_comp_right _ _ (p07s204_comp_left _ _ M.complete)
    choose A B hAB using fun i j => hB a b bNext c (M.kraus i j)
    have hb : ∀ i, (krausApply (E i) rho).PosSemidef := fun i => p07s204_kraus_psd _ h
    refine ⟨?_, ?_, ?_⟩
    · simp only [threePartyBranches, p07s204_flat, ← Fin.sum_univ_def]
      exact (Finset.sum_le_sum fun i _ => (ih i _ (hb i)).1).trans
        (p07s204_step (f a b c) (f a bNext c) M.multiplicity E hcomp A B hAB rho h)
    · simp only [threePartyBranches, p07s204_flat, ← Fin.sum_univ_def]
      rw [Finset.sum_congr rfl fun i _ => (ih i _ (hb i)).2.1]
      exact p07s204_trace_kraus _ E hcomp rho
    · intro X hX
      simp only [threePartyBranches, List.mem_flatMap] at hX
      obtain ⟨i, _, hi⟩ := hX
      exact (ih i _ (hb i)).2.2 X hi
  | @charlie a b c x y z cNext o hpos M next ih =>
    intro rho h
    let E := fun i j => Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ)
      (Matrix.kronecker (1 : Matrix (Fin b) (Fin b) ℂ) (M.kraus i j))
    have hcomp : ∑ i, ∑ j, (E i j)ᴴ * E i j = 1 :=
      p07s204_comp_right _ _ (p07s204_comp_right _ _ M.complete)
    choose A B hAB using fun i j => hC a b c cNext (M.kraus i j)
    have hb : ∀ i, (krausApply (E i) rho).PosSemidef := fun i => p07s204_kraus_psd _ h
    refine ⟨?_, ?_, ?_⟩
    · simp only [threePartyBranches, p07s204_flat, ← Fin.sum_univ_def]
      exact (Finset.sum_le_sum fun i _ => (ih i _ (hb i)).1).trans
        (p07s204_step (f a b c) (f a b cNext) M.multiplicity E hcomp A B hAB rho h)
    · simp only [threePartyBranches, p07s204_flat, ← Fin.sum_univ_def]
      rw [Finset.sum_congr rfl fun i _ => (ih i _ (hb i)).2.1]
      exact p07s204_trace_kraus _ E hcomp rho
    · intro X hX
      simp only [threePartyBranches, List.mem_flatMap] at hX
      obtain ⟨i, _, hi⟩ := hX
      exact (ih i _ (hb i)).2.2 X hi

lemma p07s204_avg_le_gen {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (X : Matrix (I × J) (I × J) ℂ) :
    (if 0 < X.trace.re then X.trace.re * negativity ((X.trace.re : ℂ)⁻¹ • X) else 0) ≤
      (traceNorm (partialTransposeFirst X) - X.trace.re) / 2 := by
  split_ifs with h
  · rw [negativity, p07s204_pt_smul, ← Complex.ofReal_inv,
      p07s204_tn_smul _ (inv_nonneg.2 h.le)]
    field_simp
    ring_nf
    rfl
  · have := p07s204_tn_nonneg (partialTransposeFirst X); linarith

lemma p07s204_final {N G H : Type*} [Fintype N] [DecidableEq N] [Fintype G] [DecidableEq G]
    [Fintype H] [DecidableEq H] (f : G × H ≃ N) (B : List (Matrix N N ℂ))
    (hpsd : ∀ X ∈ B, X.PosSemidef) (htr : (B.map Matrix.trace).sum = 1) (T : ℝ)
    (hT : (B.map fun X => traceNorm (partialTransposeFirst (X.submatrix f f))).sum ≤ T)
    (o : ℕ) (record : ℕ → Fin o) :
    ((recordedBranches B o record).map fun X => if 0 < X.trace.re then
      X.trace.re * negativity ((((X.trace.re : ℂ)⁻¹ • X)).submatrix f f) else 0).sum ≤
        (T - 1) / 2 := by
  unfold recordedBranches
  rw [List.map_ofFn, List.sum_ofFn]
  set Y : Fin o → Matrix N N ℂ := fun i =>
    ∑ j : Fin B.length, if record j.val = i then B.get j else 0 with hY
  have hBh : ∀ j : Fin B.length, (partialTransposeFirst ((B.get j).submatrix f f)).IsHermitian :=
    fun j => p07s204_pt_herm ((hpsd _ (List.get_mem B j)).submatrix f).1
  have htrs : ∀ X : Matrix N N ℂ, (X.submatrix f f).trace = X.trace := fun X => by
    unfold Matrix.trace; exact Fintype.sum_equiv f _ _ (fun _ => rfl)
  have h0 : ∀ i, (fun X : Matrix N N ℂ => if 0 < X.trace.re then
      X.trace.re * negativity ((((X.trace.re : ℂ)⁻¹ • X)).submatrix f f) else 0) (Y i) ≤
      (traceNorm (partialTransposeFirst ((Y i).submatrix f f)) - (Y i).trace.re) / 2 := by
    intro i
    have := p07s204_avg_le_gen ((Y i).submatrix f f)
    simp only [htrs, Matrix.submatrix_smul] at this
    simpa [Matrix.submatrix_smul] using this
  have h1 : ∀ i, traceNorm (partialTransposeFirst ((Y i).submatrix f f)) ≤
      ∑ j : Fin B.length, if record j.val = i then
        traceNorm (partialTransposeFirst ((B.get j).submatrix f f)) else 0 := by
    intro i
    rw [hY]
    have hsub : ∀ j : Fin B.length, (if record j.val = i then B.get j else 0).submatrix f f =
        if record j.val = i then (B.get j).submatrix f f else 0 := by
      intro j; split_ifs <;> rfl
    simp only [p07s204_submatrix_sum, hsub, p07s204_pt_sum]
    refine (p07s204_tn_finset_sum _ _ fun j _ => ?_).trans
      (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    · split_ifs
      · exact hBh j
      · rw [p07s204_pt_zero]; exact Matrix.isHermitian_zero
    · split_ifs
      · rfl
      · rw [p07s204_pt_zero, p07s204_tn_zero]
  have h2 : ∑ i, traceNorm (partialTransposeFirst ((Y i).submatrix f f)) ≤ T := by
    refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [p07s204_sum_get B (fun X => traceNorm (partialTransposeFirst (X.submatrix f f)))]
    exact hT
  have ho : 0 < o := Fin.pos (record 0)
  have h3 : ∑ i, (Y i).trace.re = 1 := by
    rw [← Complex.re_sum]
    simp only [hY, Matrix.trace_sum]
    rw [Finset.sum_comm]
    simp only [apply_ite Matrix.trace, Matrix.trace_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [p07s204_sum_get B Matrix.trace, htr]
    simp
  calc _ ≤ ∑ i, (traceNorm (partialTransposeFirst ((Y i).submatrix f f)) - (Y i).trace.re) / 2 :=
        Finset.sum_le_sum fun i _ => h0 i
    _ ≤ (T - 1) / 2 := by
        rw [← Finset.sum_div, Finset.sum_sub_distrib, h3]
        linarith

def p07s204_f0 (a b c : ℕ) : (Fin a × Fin b) × Fin c ≃ Fin a × (Fin b × Fin c) :=
  ⟨fun t => (t.1.1, (t.1.2, t.2)), fun s => ((s.1, s.2.1), s.2.2), fun _ => rfl, fun _ => rfl⟩

def p07s204_f1 (a b c : ℕ) : (Fin a × Fin c) × Fin b ≃ Fin a × (Fin b × Fin c) :=
  ⟨fun t => (t.1.1, (t.2, t.1.2)), fun s => ((s.1, s.2.2), s.2.1), fun _ => rfl, fun _ => rfl⟩

def p07s204_f2 (a b c : ℕ) : (Fin b × Fin c) × Fin a ≃ Fin a × (Fin b × Fin c) :=
  ⟨fun t => (t.2, t.1), fun s => (s.2, s.1), fun _ => rfl, fun _ => rfl⟩

section cuts
variable (a a' b b' c c' : ℕ)

lemma p07s204_c0A (K : Matrix (Fin a') (Fin a) ℂ) :
    (Matrix.kronecker K (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ)).submatrix
      (p07s204_f0 a' b c) (p07s204_f0 a b c) =
      Matrix.kronecker (Matrix.kronecker K (1 : Matrix (Fin b) (Fin b) ℂ)) (1 : Matrix (Fin c) (Fin c) ℂ) := by
  ext ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩
  simp [Matrix.kronecker, Matrix.one_apply, p07s204_f0, ite_and, mul_assoc]
  all_goals (split_ifs <;> simp_all)

lemma p07s204_c0B (K : Matrix (Fin b') (Fin b) ℂ) :
    (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ)
      (Matrix.kronecker K (1 : Matrix (Fin c) (Fin c) ℂ))).submatrix
      (p07s204_f0 a b' c) (p07s204_f0 a b c) =
      Matrix.kronecker (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) K) (1 : Matrix (Fin c) (Fin c) ℂ) := by
  ext ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩
  simp [Matrix.kronecker, Matrix.one_apply, p07s204_f0, ite_and, mul_assoc]
  all_goals (split_ifs <;> simp_all)

lemma p07s204_c0C (K : Matrix (Fin c') (Fin c) ℂ) :
    (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ)
      (Matrix.kronecker (1 : Matrix (Fin b) (Fin b) ℂ) K)).submatrix
      (p07s204_f0 a b c') (p07s204_f0 a b c) =
      Matrix.kronecker (1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) K := by
  ext ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩
  simp [Matrix.kronecker, Matrix.one_apply, p07s204_f0, ite_and, mul_assoc]
  all_goals (split_ifs <;> simp_all)

lemma p07s204_c1A (K : Matrix (Fin a') (Fin a) ℂ) :
    (Matrix.kronecker K (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ)).submatrix
      (p07s204_f1 a' b c) (p07s204_f1 a b c) =
      Matrix.kronecker (Matrix.kronecker K (1 : Matrix (Fin c) (Fin c) ℂ)) (1 : Matrix (Fin b) (Fin b) ℂ) := by
  ext ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩
  simp [Matrix.kronecker, Matrix.one_apply, p07s204_f1, ite_and, mul_assoc]
  all_goals (split_ifs <;> simp_all)

lemma p07s204_c1B (K : Matrix (Fin b') (Fin b) ℂ) :
    (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ)
      (Matrix.kronecker K (1 : Matrix (Fin c) (Fin c) ℂ))).submatrix
      (p07s204_f1 a b' c) (p07s204_f1 a b c) =
      Matrix.kronecker (1 : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) K := by
  ext ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩
  simp [Matrix.kronecker, Matrix.one_apply, p07s204_f1, ite_and, mul_assoc]
  all_goals (split_ifs <;> simp_all)

lemma p07s204_c1C (K : Matrix (Fin c') (Fin c) ℂ) :
    (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ)
      (Matrix.kronecker (1 : Matrix (Fin b) (Fin b) ℂ) K)).submatrix
      (p07s204_f1 a b c') (p07s204_f1 a b c) =
      Matrix.kronecker (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) K) (1 : Matrix (Fin b) (Fin b) ℂ) := by
  ext ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩
  simp [Matrix.kronecker, Matrix.one_apply, p07s204_f1, ite_and, mul_assoc]
  all_goals (split_ifs <;> simp_all)

lemma p07s204_c2A (K : Matrix (Fin a') (Fin a) ℂ) :
    (Matrix.kronecker K (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ)).submatrix
      (p07s204_f2 a' b c) (p07s204_f2 a b c) =
      Matrix.kronecker (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ) K := by
  ext ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩
  simp [Matrix.kronecker, Matrix.one_apply, p07s204_f2, ite_and, mul_comm]
  all_goals (split_ifs <;> simp_all)

lemma p07s204_c2B (K : Matrix (Fin b') (Fin b) ℂ) :
    (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ)
      (Matrix.kronecker K (1 : Matrix (Fin c) (Fin c) ℂ))).submatrix
      (p07s204_f2 a b' c) (p07s204_f2 a b c) =
      Matrix.kronecker (Matrix.kronecker K (1 : Matrix (Fin c) (Fin c) ℂ)) (1 : Matrix (Fin a) (Fin a) ℂ) := by
  ext ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩
  simp [Matrix.kronecker, Matrix.one_apply, p07s204_f2, ite_and, mul_comm]
  all_goals (split_ifs <;> simp_all)

lemma p07s204_c2C (K : Matrix (Fin c') (Fin c) ℂ) :
    (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ)
      (Matrix.kronecker (1 : Matrix (Fin b) (Fin b) ℂ) K)).submatrix
      (p07s204_f2 a b c') (p07s204_f2 a b c) =
      Matrix.kronecker (Matrix.kronecker (1 : Matrix (Fin b) (Fin b) ℂ) K) (1 : Matrix (Fin a) (Fin a) ℂ) := by
  ext ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩
  simp [Matrix.kronecker, Matrix.one_apply, p07s204_f2, ite_and, mul_comm]
  all_goals (split_ifs <;> simp_all)

end cuts

open QAlgorithms QAlgorithms.Entanglement QAlgorithms.Papers.Independent.Independent1.P07 in
theorem solution {a b c x y z : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (P : ThreePartyProtocol a b c x y z) (o : ℕ) (record : ℕ → Fin o)
    (rho : Matrix (Fin a × (Fin b × Fin c)) (Fin a × (Fin b × Fin c)) ℂ)
    (hrho : IsDensityMatrix rho) :
    ∀ k : Fin 3,
      ((recordedBranches (threePartyBranches P rho) o record).map fun X => if 0 < X.trace.re then
        X.trace.re*threePartyMeasures ((X.trace.re : ℂ)⁻¹ • X) (Fin.castAdd 3 k) else 0).sum ≤
          threePartyMeasures rho (Fin.castAdd 3 k) := by
  intro k
  fin_cases k
  · obtain ⟨hT, htr, hpsd⟩ := p07s204_tree3 (fun a b _ => Fin a × Fin b) (fun _ _ c => Fin c)
      p07s204_f0 (fun a a' b c K => ⟨_, _, p07s204_c0A a a' b c K⟩)
      (fun a b b' c K => ⟨_, _, p07s204_c0B a b b' c K⟩)
      (fun a b c c' K => ⟨_, _, p07s204_c0C a b c c' K⟩) P rho hrho.1
    exact p07s204_final (p07s204_f0 x y z) _ hpsd (by rw [htr, hrho.2]) _ hT o record
  · obtain ⟨hT, htr, hpsd⟩ := p07s204_tree3 (fun a _ c => Fin a × Fin c) (fun _ b _ => Fin b)
      p07s204_f1 (fun a a' b c K => ⟨_, _, p07s204_c1A a a' b c K⟩)
      (fun a b b' c K => ⟨_, _, p07s204_c1B a b b' c K⟩)
      (fun a b c c' K => ⟨_, _, p07s204_c1C a b c c' K⟩) P rho hrho.1
    exact p07s204_final (p07s204_f1 x y z) _ hpsd (by rw [htr, hrho.2]) _ hT o record
  · obtain ⟨hT, htr, hpsd⟩ := p07s204_tree3 (fun _ b c => Fin b × Fin c) (fun a _ _ => Fin a)
      p07s204_f2 (fun a a' b c K => ⟨_, _, p07s204_c2A a a' b c K⟩)
      (fun a b b' c K => ⟨_, _, p07s204_c2B a b b' c K⟩)
      (fun a b c c' K => ⟨_, _, p07s204_c2C a b c c' K⟩) P rho hrho.1
    exact p07s204_final (p07s204_f2 x y z) _ hpsd (by rw [htr, hrho.2]) _ hT o record
