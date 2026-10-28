-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P07.robustness_locc
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T17:26:00.60792+00:00
-- url     : https://prove2.me/submissions/be8366a0-2d2c-4708-8dcf-ae390c576853

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


def p07s204_SepCone {I J : Type*} [Fintype I] [Fintype J] (X : Matrix (I × J) (I × J) ℂ) : Prop :=
  ∃ (T : Type) (_ : Fintype T) (A : T → Matrix I I ℂ) (B : T → Matrix J J ℂ),
    (∀ t, (A t).PosSemidef ∧ (B t).PosSemidef) ∧ X = ∑ t, Matrix.kronecker (A t) (B t)

def p07s204_PPTCone {I J : Type*} [Fintype I] [Fintype J] (X : Matrix (I × J) (I × J) ℂ) : Prop :=
  X.PosSemidef ∧ (partialTransposeFirst X).PosSemidef

section cones
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma p07s204_sep_zero : p07s204_SepCone (0 : Matrix (I × J) (I × J) ℂ) :=
  ⟨Empty, inferInstance, fun _ => 0, fun _ => 0, fun t => t.elim, by simp⟩

lemma p07s204_sep_add {X Y : Matrix (I × J) (I × J) ℂ} (hX : p07s204_SepCone X)
    (hY : p07s204_SepCone Y) : p07s204_SepCone (X + Y) := by
  obtain ⟨T, _, A, B, hAB, rfl⟩ := hX
  obtain ⟨T', _, A', B', hAB', rfl⟩ := hY
  refine ⟨T ⊕ T', inferInstance, Sum.elim A A', Sum.elim B B', ?_, ?_⟩
  · rintro (t | t)
    · exact hAB t
    · exact hAB' t
  · rw [Fintype.sum_sum_type]; rfl

lemma p07s204_sep_psd {X : Matrix (I × J) (I × J) ℂ} (hX : p07s204_SepCone X) : X.PosSemidef := by
  obtain ⟨T, _, A, B, hAB, rfl⟩ := hX
  exact Matrix.posSemidef_sum _ fun t _ => (hAB t).1.kronecker (hAB t).2

lemma p07s204_sep_sum {ι : Type*} (s : Finset ι) (F : ι → Matrix (I × J) (I × J) ℂ)
    (hF : ∀ i ∈ s, p07s204_SepCone (F i)) : p07s204_SepCone (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using p07s204_sep_zero
  | insert x s hx ih =>
    rw [Finset.sum_insert hx]
    exact p07s204_sep_add (hF x (by simp)) (ih fun i hi => hF i (by simp [hi]))

lemma p07s204_kron_conj {I' J' : Type*} [Fintype I'] [Fintype J'] (P : Matrix I' I ℂ)
    (Q : Matrix J' J ℂ) (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    Matrix.kronecker P Q * Matrix.kronecker A B * (Matrix.kronecker P Q)ᴴ =
      Matrix.kronecker (P * A * Pᴴ) (Q * B * Qᴴ) := by
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

lemma p07s204_sep_kraus {I' J' : Type*} [Fintype I'] [Fintype J'] {Kt : Type} [Fintype Kt]
    (P : Kt → Matrix I' I ℂ) (Q : Kt → Matrix J' J ℂ) {X : Matrix (I × J) (I × J) ℂ}
    (hX : p07s204_SepCone X) :
    p07s204_SepCone (krausApply (fun j => Matrix.kronecker (P j) (Q j)) X) := by
  obtain ⟨T, _, A, B, hAB, rfl⟩ := hX
  refine ⟨Kt × T, inferInstance, fun p => P p.1 * A p.2 * (P p.1)ᴴ,
    fun p => Q p.1 * B p.2 * (Q p.1)ᴴ, fun p => ⟨(hAB p.2).1.mul_mul_conjTranspose_same _,
      (hAB p.2).2.mul_mul_conjTranspose_same _⟩, ?_⟩
  simp only [krausApply, Matrix.mul_sum, Matrix.sum_mul, p07s204_kron_conj]
  rw [Fintype.sum_prod_type]

lemma p07s204_pt_kron (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    partialTransposeFirst (Matrix.kronecker A B) = Matrix.kronecker A.transpose B := by
  ext p q; simp [partialTransposeFirst, Matrix.kronecker]

lemma p07s204_sep_ppt {X : Matrix (I × J) (I × J) ℂ} (hX : p07s204_SepCone X) :
    p07s204_PPTCone X := by
  refine ⟨p07s204_sep_psd hX, ?_⟩
  obtain ⟨T, _, A, B, hAB, rfl⟩ := hX
  rw [p07s204_pt_sum]
  exact Matrix.posSemidef_sum _ fun t _ => by
    rw [p07s204_pt_kron]; exact (hAB t).1.transpose.kronecker (hAB t).2

lemma p07s204_ppt_zero : p07s204_PPTCone (0 : Matrix (I × J) (I × J) ℂ) := by
  refine ⟨Matrix.PosSemidef.zero, ?_⟩
  rw [p07s204_pt_zero]; exact Matrix.PosSemidef.zero

lemma p07s204_ppt_add {X Y : Matrix (I × J) (I × J) ℂ} (hX : p07s204_PPTCone X)
    (hY : p07s204_PPTCone Y) : p07s204_PPTCone (X + Y) :=
  ⟨hX.1.add hY.1, by rw [p07s204_pt_add]; exact hX.2.add hY.2⟩

lemma p07s204_ppt_sum {ι : Type*} (s : Finset ι) (F : ι → Matrix (I × J) (I × J) ℂ)
    (hF : ∀ i ∈ s, p07s204_PPTCone (F i)) : p07s204_PPTCone (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using p07s204_ppt_zero
  | insert x s hx ih =>
    rw [Finset.sum_insert hx]
    exact p07s204_ppt_add (hF x (by simp)) (ih fun i hi => hF i (by simp [hi]))

lemma p07s204_ppt_kraus {I' J' : Type*} [Fintype I'] [Fintype J'] [DecidableEq J'] {Kt : Type}
    [Fintype Kt] (P : Kt → Matrix I' I ℂ) (Q : Kt → Matrix J' J ℂ) {X : Matrix (I × J) (I × J) ℂ}
    (hX : p07s204_PPTCone X) :
    p07s204_PPTCone (krausApply (fun j => Matrix.kronecker (P j) (Q j)) X) := by
  refine ⟨p07s204_kraus_psd _ hX.1, ?_⟩
  simp only [krausApply, p07s204_pt_sum, p07s204_pt_prod]
  exact p07s204_kraus_psd _ hX.2

end cones

lemma p07s204_norm {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] {P : Matrix n n ℂ}
    (hP : P.PosSemidef) :
    ∃ r : Matrix n n ℂ, IsDensityMatrix r ∧ P = ((P.trace.re : ℝ) : ℂ) • r := by
  obtain ⟨h0, htr⟩ := p07s204_tr_real hP
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

lemma p07s204_psd4 {I : Type*} [Fintype I] [DecidableEq I] (E : Matrix I I ℂ) :
    ∃ α : Fin 4 → ℂ, ∃ A : Fin 4 → Matrix I I ℂ, (∀ s, (A s).PosSemidef) ∧
      E = ∑ s, α s • A s := by
  set R : Matrix I I ℂ := (1 / 2 : ℂ) • (E + Eᴴ)
  set S : Matrix I I ℂ := (-Complex.I / 2) • (E - Eᴴ)
  have hR : R.IsHermitian := by
    ext i j
    simp only [R, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    simp [star_star]; ring
  have hS : S.IsHermitian := by
    ext i j
    simp only [S, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    simp [star_star]; ring
  have hE : E = R + Complex.I • S := by
    simp only [R, S, smul_smul]
    rw [show Complex.I * (-Complex.I / 2) = 1 / 2 by
      rw [mul_div_assoc', mul_neg, Complex.I_mul_I]; ring]
    rw [← smul_add]; ext i j; simp; ring
  have eR := p07s204_parts R hR
  have eS := p07s204_parts S hS
  refine ⟨![1, -1, Complex.I, -Complex.I],
    ![cfc (fun t : ℝ => max t 0) R, cfc (fun t : ℝ => max (-t) 0) R,
      cfc (fun t : ℝ => max t 0) S, cfc (fun t : ℝ => max (-t) 0) S], ?_, ?_⟩
  · intro s
    fin_cases s <;> exact p07s204_cfc_psd _ _ (fun t => le_max_right _ _)
  · rw [Fin.sum_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, one_smul, neg_smul]
    conv_lhs => rw [hE, ← eR, ← eS]
    rw [smul_sub]; abel

lemma p07s204_kron_bilin {I J ι κ : Type*} [Fintype ι] [Fintype κ] (a : ι → ℂ) (X : ι → Matrix I I ℂ)
    (b : κ → ℂ) (Y : κ → Matrix J J ℂ) :
    Matrix.kronecker (∑ s, a s • X s) (∑ s', b s' • Y s') =
      ∑ s, ∑ s', (a s * b s') • Matrix.kronecker (X s) (Y s') := by
  ext p q
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma p07s204_span {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M : Matrix (I × J) (I × J) ℂ) :
    ∃ (T : Type) (_ : Fintype T) (c : T → ℂ) (A : T → Matrix I I ℂ) (B : T → Matrix J J ℂ),
      (∀ t, (A t).PosSemidef ∧ (B t).PosSemidef) ∧ M = ∑ t, c t • Matrix.kronecker (A t) (B t) := by
  choose α A hA hE using fun E : Matrix I I ℂ => p07s204_psd4 E
  choose β B hB hF using fun E : Matrix J J ℂ => p07s204_psd4 E
  refine ⟨(I × J) × ((I × J) × (Fin 4 × Fin 4)), inferInstance,
    fun t => α (Matrix.single t.1.1 t.2.1.1 (M t.1 t.2.1)) t.2.2.1 *
      β (Matrix.single t.1.2 t.2.1.2 1) t.2.2.2,
    fun t => A (Matrix.single t.1.1 t.2.1.1 (M t.1 t.2.1)) t.2.2.1,
    fun t => B (Matrix.single t.1.2 t.2.1.2 1) t.2.2.2,
    fun t => ⟨hA _ _, hB _ _⟩, ?_⟩
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  conv_rhs => rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  conv_rhs => rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  conv_rhs => rw [Fintype.sum_prod_type]
  have e1 : Matrix.single p q (M p q) =
      Matrix.kronecker (Matrix.single p.1 q.1 (M p q)) (Matrix.single p.2 q.2 (1 : ℂ)) := by
    simp only [Matrix.kronecker]; rw [Matrix.single_kronecker_single, mul_one]
  rw [e1]
  conv_lhs => rw [hE (Matrix.single p.1 q.1 (M p q)), hF (Matrix.single p.2 q.2 (1 : ℂ))]
  rw [p07s204_kron_bilin]

lemma p07s204_sep_span {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {H : Matrix (I × J) (I × J) ℂ} (hH : H.IsHermitian) :
    ∃ P N, p07s204_SepCone P ∧ p07s204_SepCone N ∧ H = P - N := by
  obtain ⟨T, _, c, A, B, hAB, hHe⟩ := p07s204_span H
  have hK : ∀ t, (Matrix.kronecker (A t) (B t)).IsHermitian := fun t =>
    ((hAB t).1.kronecker (hAB t).2).1
  have h1 : Hᴴ = ∑ t, star (c t) • Matrix.kronecker (A t) (B t) := by
    conv_lhs => rw [hHe]
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [Matrix.conjTranspose_smul, (hK t).eq]
  have h2 : H = ∑ t, (((c t).re : ℝ) : ℂ) • Matrix.kronecker (A t) (B t) := by
    have e : H = (1 / 2 : ℂ) • (H + Hᴴ) := by
      rw [hH.eq, ← two_smul ℂ H, smul_smul]; norm_num
    rw [e, h1]
    conv_lhs => rw [hHe]
    rw [← Finset.sum_add_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← add_smul, smul_smul]
    congr 1
    apply Complex.ext <;> simp <;> ring
  refine ⟨∑ t, ((max (c t).re 0 : ℝ) : ℂ) • Matrix.kronecker (A t) (B t),
    ∑ t, ((max (-(c t).re) 0 : ℝ) : ℂ) • Matrix.kronecker (A t) (B t), ?_, ?_, ?_⟩
  · refine ⟨T, inferInstance, fun t => ((max (c t).re 0 : ℝ) : ℂ) • A t, B, fun t =>
      ⟨(hAB t).1.smul (Complex.zero_le_real.mpr (le_max_right _ _)), (hAB t).2⟩, ?_⟩
    simp only [Matrix.kronecker, Matrix.smul_kronecker]
  · refine ⟨T, inferInstance, fun t => ((max (-(c t).re) 0 : ℝ) : ℂ) • A t, B, fun t =>
      ⟨(hAB t).1.smul (Complex.zero_le_real.mpr (le_max_right _ _)), (hAB t).2⟩, ?_⟩
    simp only [Matrix.kronecker, Matrix.smul_kronecker]
  · rw [h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← sub_smul, ← Complex.ofReal_sub]
    congr 2
    rcases le_total (c t).re 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring

lemma p07s204_prod_state {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J] :
    ∃ s0 : Matrix (I × J) (I × J) ℂ, IsDensityMatrix s0 ∧ p07s204_SepCone s0 ∧
      IsSeparableDensity s0 := by
  obtain ⟨rI, hrI, -⟩ := p07s204_norm (Matrix.PosSemidef.one (n := I) (R := ℂ))
  obtain ⟨rJ, hrJ, -⟩ := p07s204_norm (Matrix.PosSemidef.one (n := J) (R := ℂ))
  refine ⟨Matrix.kronecker rI rJ, ⟨hrI.1.kronecker hrJ.1, ?_⟩,
    ⟨Unit, inferInstance, fun _ => rI, fun _ => rJ, fun _ => ⟨hrI.1, hrJ.1⟩, by simp⟩,
    ⟨1, fun _ => 1, fun _ => rI, fun _ => rJ, fun _ => zero_le_one, by simp,
      fun _ => ⟨hrI, hrJ⟩, by simp⟩⟩
  rw [Matrix.kronecker, Matrix.trace_kronecker, hrI.2, hrJ.2, one_mul]

lemma p07s204_sep_norm {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J] {X : Matrix (I × J) (I × J) ℂ} (hX : p07s204_SepCone X) :
    ∃ s ∈ (separableBase : Set (Matrix (I × J) (I × J) ℂ)), X = ((X.trace.re : ℝ) : ℂ) • s := by
  have hXp := p07s204_sep_psd hX
  by_cases hx0 : X.trace.re = 0
  · obtain ⟨s0, -, -, hs0⟩ := p07s204_prod_state (I := I) (J := J)
    refine ⟨s0, hs0, ?_⟩
    have : X.trace = 0 := by rw [(p07s204_tr_real hXp).2, hx0]; simp
    rw [hXp.trace_eq_zero_iff.mp this]; simp
  obtain ⟨T, _, A, B, hAB, rfl⟩ := hX
  choose a ha hA' using fun t => p07s204_norm (hAB t).1
  choose b hb hB' using fun t => p07s204_norm (hAB t).2
  set x := (∑ t, Matrix.kronecker (A t) (B t)).trace.re with hxdef
  have hx0' : 0 < x := lt_of_le_of_ne (p07s204_tr_real hXp).1 (Ne.symm hx0)
  have hk : ∀ t, Matrix.kronecker (A t) (B t) =
      (((A t).trace.re * (B t).trace.re : ℝ) : ℂ) • Matrix.kronecker (a t) (b t) := by
    intro t
    conv_lhs => rw [hA' t, hB' t]
    simp only [Matrix.kronecker, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul]
    push_cast; ring_nf
  have hxs : x = ∑ t, (A t).trace.re * (B t).trace.re := by
    rw [hxdef, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Matrix.kronecker, Matrix.trace_kronecker, (p07s204_tr_real (hAB t).1).2,
      (p07s204_tr_real (hAB t).2).2]
    simp
  let e := Fintype.equivFin T
  refine ⟨∑ t, (((A t).trace.re * (B t).trace.re / x : ℝ) : ℂ) • Matrix.kronecker (a t) (b t),
    ⟨Fintype.card T, fun j => (A (e.symm j)).trace.re * (B (e.symm j)).trace.re / x,
      fun j => a (e.symm j), fun j => b (e.symm j), fun j => ?_, ?_, fun j => ⟨ha _, hb _⟩, ?_⟩, ?_⟩
  · exact div_nonneg (mul_nonneg (p07s204_tr_real (hAB _).1).1 (p07s204_tr_real (hAB _).2).1)
      hx0'.le
  · rw [Equiv.sum_comp e.symm (fun t => (A t).trace.re * (B t).trace.re / x), ← Finset.sum_div,
      ← hxs, div_self hx0'.ne']
  · exact (Equiv.sum_comp e.symm (fun t =>
      (((A t).trace.re * (B t).trace.re / x : ℝ) : ℂ) • Matrix.kronecker (a t) (b t))).symm
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_smul, ← Complex.ofReal_mul, mul_div_cancel₀ _ hx0'.ne', hk t]

lemma p07s204_ppt_norm {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J] {X : Matrix (I × J) (I × J) ℂ} (hX : p07s204_PPTCone X) :
    ∃ s ∈ (pptBase : Set (Matrix (I × J) (I × J) ℂ)), X = ((X.trace.re : ℝ) : ℂ) • s := by
  by_cases hx0 : X.trace.re = 0
  · obtain ⟨s0, hs0, hs0c, -⟩ := p07s204_prod_state (I := I) (J := J)
    refine ⟨s0, ⟨hs0, (p07s204_sep_ppt hs0c).2⟩, ?_⟩
    have : X.trace = 0 := by rw [(p07s204_tr_real hX.1).2, hx0]; simp
    rw [hX.1.trace_eq_zero_iff.mp this]; simp
  have hx0' : 0 < X.trace.re := lt_of_le_of_ne (p07s204_tr_real hX.1).1 (Ne.symm hx0)
  refine ⟨((X.trace.re⁻¹ : ℝ) : ℂ) • X, ⟨⟨hX.1.smul (Complex.zero_le_real.mpr (by positivity)), ?_⟩,
    ?_⟩, ?_⟩
  · rw [Matrix.trace_smul, smul_eq_mul, (p07s204_tr_real hX.1).2, ← Complex.ofReal_mul,
      Complex.ofReal_re, inv_mul_cancel₀ hx0]; simp
  · rw [p07s204_pt_smul]; exact hX.2.smul (Complex.zero_le_real.mpr (by positivity))
  · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hx0]; simp

lemma p07s204_sep_of_mem {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    {s : Matrix (I × J) (I × J) ℂ} (hs : s ∈ (separableBase : Set (Matrix (I × J) (I × J) ℂ)))
    {r : ℝ} (hr : 0 ≤ r) : p07s204_SepCone ((r : ℂ) • s) ∧ s.trace = 1 := by
  obtain ⟨q, w, A, B, hw, hw1, hAB, rfl⟩ := hs
  refine ⟨⟨Fin q, inferInstance, fun j => ((r * w j : ℝ) : ℂ) • A j, B, fun j =>
    ⟨(hAB j).1.1.smul (Complex.zero_le_real.mpr (mul_nonneg hr (hw j))), (hAB j).2.1⟩, ?_⟩, ?_⟩
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.kronecker, Matrix.smul_kronecker, smul_smul]; push_cast; rfl
  · rw [Matrix.trace_sum]
    simp only [Matrix.trace_smul, Matrix.kronecker, Matrix.trace_kronecker, (hAB _).1.2,
      (hAB _).2.2, mul_one, smul_eq_mul]
    rw [← Complex.ofReal_sum, hw1]; simp

lemma p07s204_ppt_of_mem {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {s : Matrix (I × J) (I × J) ℂ} (hs : s ∈ (pptBase : Set (Matrix (I × J) (I × J) ℂ)))
    {r : ℝ} (hr : 0 ≤ r) : p07s204_PPTCone ((r : ℂ) • s) ∧ s.trace = 1 :=
  ⟨⟨hs.1.1.smul (Complex.zero_le_real.mpr hr), by
    rw [p07s204_pt_smul]; exact hs.2.smul (Complex.zero_le_real.mpr hr)⟩, hs.1.2⟩

theorem p07s204_tree_dec (C : (a b : ℕ) → Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ → Prop)
    (hK : ∀ {a b a' b' : ℕ} {Kt : Type} [Fintype Kt] (P : Kt → Matrix (Fin a') (Fin a) ℂ)
      (Q : Kt → Matrix (Fin b') (Fin b) ℂ) (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ),
      C a b X → C a' b' (krausApply (fun j => Matrix.kronecker (P j) (Q j)) X))
    {a b c d : ℕ} (P : Protocol a b c d) :
    ∀ Xp Xn : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ, C a b Xp → C a b Xn →
      ∃ L : List (Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ × Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ),
        L.map (fun p => p.1 - p.2) = protocolBranches P (Xp - Xn) ∧
        (∀ p ∈ L, C c d p.1 ∧ C c d p.2) ∧ (L.map fun p => p.2.trace).sum = Xn.trace := by
  induction P with
  | finish a b =>
    intro Xp Xn hp hn
    exact ⟨[(Xp, Xn)], by simp [protocolBranches], by simp [hp, hn], by simp⟩
  | @alice a b c d aNext o hpos M next ih =>
    intro Xp Xn hp hn
    choose L hL1 hL2 hL3 using fun i => ih i _ _
      (hK (M.kraus i) (fun _ => (1 : Matrix (Fin b) (Fin b) ℂ)) Xp hp)
      (hK (M.kraus i) (fun _ => (1 : Matrix (Fin b) (Fin b) ℂ)) Xn hn)
    refine ⟨(List.finRange o).flatMap L, ?_, ?_, ?_⟩
    · rw [List.map_flatMap]; simp only [protocolBranches]
      congr 1; funext i; rw [hL1 i, p07s204_kraus_sub]
    · intro p hp'
      rw [List.mem_flatMap] at hp'
      obtain ⟨i, _, hi⟩ := hp'
      exact hL2 i p hi
    · rw [p07s204_flat, ← Fin.sum_univ_def]
      simp only [hL3]
      exact p07s204_trace_alice M Xn
  | @bob a b c d bNext o hpos M next ih =>
    intro Xp Xn hp hn
    choose L hL1 hL2 hL3 using fun i => ih i _ _
      (hK (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) (M.kraus i) Xp hp)
      (hK (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) (M.kraus i) Xn hn)
    refine ⟨(List.finRange o).flatMap L, ?_, ?_, ?_⟩
    · rw [List.map_flatMap]; simp only [protocolBranches]
      congr 1; funext i; rw [hL1 i, p07s204_kraus_sub]
    · intro p hp'
      rw [List.mem_flatMap] at hp'
      obtain ⟨i, _, hi⟩ := hp'
      exact hL2 i p hi
    · rw [p07s204_flat, ← Fin.sum_univ_def]
      simp only [hL3]
      exact p07s204_trace_bob M Xn

lemma p07s204_term_le {n : Type*} [Fintype n] (S : Set (Matrix n n ℂ))
    (C : Matrix n n ℂ → Prop)
    (hnorm : ∀ X, C X → ∃ s ∈ S, X = ((X.trace.re : ℝ) : ℂ) • s)
    (hpsd : ∀ X, C X → X.PosSemidef) {P N : Matrix n n ℂ} (hP : C P) (hN : C N) :
    (if 0 < (P - N).trace.re then
      (P - N).trace.re * baseNeg S (((P - N).trace.re : ℂ)⁻¹ • (P - N)) else 0) ≤ N.trace.re := by
  have hN0 := (p07s204_tr_real (hpsd N hN)).1
  split_ifs with h
  · set p := (P - N).trace.re
    obtain ⟨sp, hsp, hPe⟩ := hnorm P hP
    obtain ⟨sn, hsn, hNe⟩ := hnorm N hN
    have hP0 := (p07s204_tr_real (hpsd P hP)).1
    have hdec : BaseDecomposition S ((p : ℂ)⁻¹ • (P - N)) (P.trace.re / p) (N.trace.re / p) sp sn := by
      refine ⟨div_nonneg hP0 h.le, div_nonneg hN0 h.le, hsp, hsn, ?_⟩
      conv_lhs => rw [hPe, hNe]
      simp only [smul_sub, smul_smul, Complex.ofReal_div, div_eq_inv_mul, Complex.ofReal_mul,
        Complex.ofReal_inv]
    have hle : baseNeg S ((p : ℂ)⁻¹ • (P - N)) ≤ N.trace.re / p := by
      refine csInf_le ⟨0, fun v hv => ?_⟩ ⟨_, _, _, _, hdec, rfl⟩
      obtain ⟨_, am, _, _, hd, rfl⟩ := hv
      exact hd.2.1
    calc p * baseNeg S ((p : ℂ)⁻¹ • (P - N)) ≤ p * (N.trace.re / p) :=
          mul_le_mul_of_nonneg_left hle h.le
      _ = N.trace.re := by field_simp
  · exact hN0

lemma p07s204_list_re {α : Type*} (L : List α) (g : α → ℂ) :
    (L.map fun p => (g p).re).sum = ((L.map g).sum).re := by
  induction L with
  | nil => simp
  | cons x L ih => simp [ih]

lemma p07s204_final_rob {c d : ℕ} (S : Set (Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ))
    (C : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ → Prop)
    (hnorm : ∀ X, C X → ∃ s ∈ S, X = ((X.trace.re : ℝ) : ℂ) • s)
    (hpsd : ∀ X, C X → X.PosSemidef) (h0 : C 0)
    (hsum : ∀ (n : ℕ) (F : Fin n → Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ),
      (∀ j, C (F j)) → C (∑ j, F j))
    (L : List (Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ × Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ))
    (hL : ∀ p ∈ L, C p.1 ∧ C p.2) (o : ℕ) (record : ℕ → Fin o) :
    selectiveAverage (baseNeg S) (recordedBranches (L.map fun p => p.1 - p.2) o record) ≤
      (L.map fun p => p.2.trace.re).sum := by
  unfold selectiveAverage recordedBranches
  rw [List.map_ofFn, List.sum_ofFn]
  set B := L.map fun p => p.1 - p.2 with hB
  have hlen : B.length = L.length := List.length_map _
  set Lp : Fin B.length → Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ :=
    fun j => (L.get (Fin.cast hlen j)).1 with hLp
  set Ln : Fin B.length → Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ :=
    fun j => (L.get (Fin.cast hlen j)).2 with hLn
  have hget : ∀ j, B.get j = Lp j - Ln j := fun j => by simp [B, Lp, Ln]
  have hCp : ∀ j, C (Lp j) := fun j => (hL _ (List.get_mem L _)).1
  have hCn : ∀ j, C (Ln j) := fun j => (hL _ (List.get_mem L _)).2
  have hY : ∀ k : Fin o, (∑ j : Fin B.length, if record j.val = k then B.get j else 0) =
      (∑ j, if record j.val = k then Lp j else 0) - (∑ j, if record j.val = k then Ln j else 0) := by
    intro k
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · exact hget j
    · simp
  have hite : ∀ (k : Fin o) (F : Fin B.length → Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ),
      (∀ j, C (F j)) → C (∑ j, if record j.val = k then F j else 0) := by
    intro k F hF
    exact hsum _ _ fun j => by split_ifs; exacts [hF j, h0]
  calc _ ≤ ∑ k : Fin o, (∑ j : Fin B.length, if record j.val = k then Ln j else 0).trace.re := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [Function.comp_apply, hY k]
        exact p07s204_term_le S C hnorm hpsd (hite k _ hCp) (hite k _ hCn)
    _ = ∑ j : Fin B.length, (Ln j).trace.re := by
        simp only [Matrix.trace_sum, Complex.re_sum, apply_ite Matrix.trace, Matrix.trace_zero,
          apply_ite Complex.re, Complex.zero_re]
        rw [Finset.sum_comm]
        simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    _ = (L.map fun p => p.2.trace.re).sum := by
        rw [← p07s204_sum_get L (fun p => p.2.trace.re)]
        exact Fintype.sum_equiv (finCongr hlen) _ _ (fun _ => rfl)

open QAlgorithms QAlgorithms.Entanglement QAlgorithms.Papers.Independent.Independent1.P07 in
theorem solution {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (P : Protocol a b c d) (o : ℕ) (record : ℕ → Fin o)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hrho : IsDensityMatrix rho) :
    letI : Nonempty (Fin a) := ⟨⟨0,ha⟩⟩
    letI : Nonempty (Fin b) := ⟨⟨0,hb⟩⟩
    letI : Nonempty (Fin c) := ⟨⟨0,hc⟩⟩
    letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
    selectiveAverage separableRobustness (recordedBranches (protocolBranches P rho) o record) ≤ separableRobustness rho ∧
    selectiveAverage pptRobustness (recordedBranches (protocolBranches P rho) o record) ≤ pptRobustness rho := by
  haveI : Nonempty (Fin a) := ⟨⟨0,ha⟩⟩
  haveI : Nonempty (Fin b) := ⟨⟨0,hb⟩⟩
  haveI : Nonempty (Fin c) := ⟨⟨0,hc⟩⟩
  haveI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  obtain ⟨Pp, Nn, hP, hN, hrhoe⟩ := p07s204_sep_span hrho.1.1
  have hPp := p07s204_tr_real (p07s204_sep_psd hP)
  have hNp := p07s204_tr_real (p07s204_sep_psd hN)
  constructor
  · unfold separableRobustness baseNeg
    refine le_csInf ?_ ?_
    · obtain ⟨sp, hsp, hPe⟩ := p07s204_sep_norm hP
      obtain ⟨sn, hsn, hNe⟩ := p07s204_sep_norm hN
      exact ⟨_, _, _, sp, sn, ⟨hPp.1, hNp.1, hsp, hsn, by rw [hrhoe, ← hPe, ← hNe]⟩, rfl⟩
    · rintro v ⟨ap, am, rp, rm, ⟨hap, ham, hrp, hrm, he⟩, rfl⟩
      obtain ⟨hcp, -⟩ := p07s204_sep_of_mem hrp hap
      obtain ⟨hcn, htrn⟩ := p07s204_sep_of_mem hrm ham
      obtain ⟨L, hL1, hL2, hL3⟩ := p07s204_tree_dec (fun _ _ X => p07s204_SepCone X)
        (fun P Q X hX => p07s204_sep_kraus P Q hX) P _ _ hcp hcn
      rw [← he] at hL1
      rw [← hL1]
      refine (p07s204_final_rob _ (fun X => p07s204_SepCone X) (fun X hX => p07s204_sep_norm hX)
        (fun X hX => p07s204_sep_psd hX) p07s204_sep_zero
        (fun n F hF => p07s204_sep_sum _ F fun j _ => hF j) L hL2 o record).trans (le_of_eq ?_)
      rw [p07s204_list_re, hL3, Matrix.trace_smul, htrn]; simp
  · unfold pptRobustness baseNeg
    refine le_csInf ?_ ?_
    · obtain ⟨sp, hsp, hPe⟩ := p07s204_ppt_norm (p07s204_sep_ppt hP)
      obtain ⟨sn, hsn, hNe⟩ := p07s204_ppt_norm (p07s204_sep_ppt hN)
      exact ⟨_, _, _, sp, sn, ⟨hPp.1, hNp.1, hsp, hsn, by rw [hrhoe, ← hPe, ← hNe]⟩, rfl⟩
    · rintro v ⟨ap, am, rp, rm, ⟨hap, ham, hrp, hrm, he⟩, rfl⟩
      obtain ⟨hcp, -⟩ := p07s204_ppt_of_mem hrp hap
      obtain ⟨hcn, htrn⟩ := p07s204_ppt_of_mem hrm ham
      obtain ⟨L, hL1, hL2, hL3⟩ := p07s204_tree_dec (fun _ _ X => p07s204_PPTCone X)
        (fun P Q X hX => p07s204_ppt_kraus P Q hX) P _ _ hcp hcn
      rw [← he] at hL1
      rw [← hL1]
      refine (p07s204_final_rob _ (fun X => p07s204_PPTCone X) (fun X hX => p07s204_ppt_norm hX)
        (fun X hX => hX.1) p07s204_ppt_zero
        (fun n F hF => p07s204_ppt_sum _ F fun j _ => hF j) L hL2 o record).trans (le_of_eq ?_)
      rw [p07s204_list_re, hL3, Matrix.trace_smul, htrn]; simp
