-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P07.negativity_hierarchy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T17:40:36.84302+00:00
-- url     : https://prove2.me/submissions/ffe05a1e-cbc8-4221-aa60-d6a52a4367e9

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

universe u v

def p07s204_SepCone {I : Type u} {J : Type v} [Fintype I] [Fintype J] (X : Matrix (I × J) (I × J) ℂ) : Prop :=
  ∃ (T : Type (max u v)) (_ : Fintype T) (A : T → Matrix I I ℂ) (B : T → Matrix J J ℂ),
    (∀ t, (A t).PosSemidef ∧ (B t).PosSemidef) ∧ X = ∑ t, Matrix.kronecker (A t) (B t)

def p07s204_PPTCone {I J : Type*} [Fintype I] [Fintype J] (X : Matrix (I × J) (I × J) ℂ) : Prop :=
  X.PosSemidef ∧ (partialTransposeFirst X).PosSemidef

section cones
variable {I : Type u} {J : Type v} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma p07s204_sep_zero : p07s204_SepCone (0 : Matrix (I × J) (I × J) ℂ) :=
  ⟨PEmpty, inferInstance, fun _ => 0, fun _ => 0, fun t => t.elim, by simp⟩

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

lemma p07s204_span {I : Type u} {J : Type v} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M : Matrix (I × J) (I × J) ℂ) :
    ∃ (T : Type (max u v)) (_ : Fintype T) (c : T → ℂ) (A : T → Matrix I I ℂ) (B : T → Matrix J J ℂ),
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

lemma p07s204_sep_span {I : Type u} {J : Type v} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
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

lemma p07s204_prod_state {I : Type u} {J : Type v} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J] :
    ∃ s0 : Matrix (I × J) (I × J) ℂ, IsDensityMatrix s0 ∧ p07s204_SepCone s0 ∧
      IsSeparableDensity s0 := by
  obtain ⟨rI, hrI, -⟩ := p07s204_norm (Matrix.PosSemidef.one (n := I) (R := ℂ))
  obtain ⟨rJ, hrJ, -⟩ := p07s204_norm (Matrix.PosSemidef.one (n := J) (R := ℂ))
  refine ⟨Matrix.kronecker rI rJ, ⟨hrI.1.kronecker hrJ.1, ?_⟩,
    ⟨PUnit, inferInstance, fun _ => rI, fun _ => rJ, fun _ => ⟨hrI.1, hrJ.1⟩, by simp⟩,
    ⟨1, fun _ => 1, fun _ => rI, fun _ => rJ, fun _ => zero_le_one, by simp,
      fun _ => ⟨hrI, hrJ⟩, by simp⟩⟩
  rw [Matrix.kronecker, Matrix.trace_kronecker, hrI.2, hrJ.2, one_mul]

lemma p07s204_sep_norm {I : Type u} {J : Type v} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
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


lemma p07s204_dens_entry {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : IsDensityMatrix A) (i j : n) : ‖A i j‖ ≤ 1 := by
  set S := cfc Real.sqrt A
  have hS : S.PosSemidef := p07s204_cfc_psd A _ (fun t => Real.sqrt_nonneg t)
  have hSS : Sᴴ * S = A := by rw [hS.1.eq]; exact p07s204_sqrt_sq hA.1
  have hdiag : ∀ k, (A k k).re = ∑ l, ‖S l k‖ ^ 2 := by
    intro k
    rw [← hSS, Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.conjTranspose_apply, Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.mul_re]
  have htr : ∑ k, (A k k).re = 1 := by
    have := congrArg Complex.re hA.2
    rwa [Matrix.trace, Complex.re_sum] at this
  have hdle : ∀ k, (A k k).re ≤ 1 := by
    intro k
    rw [← htr]
    exact Finset.single_le_sum (f := fun k => (A k k).re)
      (fun k _ => by rw [hdiag]; positivity) (Finset.mem_univ k)
  calc ‖A i j‖ = ‖∑ l, star (S l i) * S l j‖ := by
        rw [← hSS, Matrix.mul_apply]; simp [Matrix.conjTranspose_apply]
    _ ≤ ∑ l, ‖S l i‖ * ‖S l j‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => ?_))
        rw [norm_mul, norm_star]
    _ ≤ ∑ l, (‖S l i‖ ^ 2 + ‖S l j‖ ^ 2) / 2 := by
        refine Finset.sum_le_sum fun l _ => ?_
        nlinarith [sq_nonneg (‖S l i‖ - ‖S l j‖)]
    _ = ((A i i).re + (A j j).re) / 2 := by
        rw [hdiag, hdiag, ← Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ 1 := by linarith [hdle i, hdle j]

lemma p07s204_psd_closed {n : Type*} [Fintype n] :
    IsClosed {A : Matrix n n ℂ | A.PosSemidef} := by
  have e : {A : Matrix n n ℂ | A.PosSemidef} = {A | Aᴴ = A} ∩
      ⋂ x : n → ℂ, ({A | 0 ≤ (star x ⬝ᵥ A *ᵥ x).re} ∩ {A | (star x ⬝ᵥ A *ᵥ x).im = 0}) := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec, Complex.nonneg_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun x => ⟨(h2 x).1, (h2 x).2.symm⟩⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun x => ⟨(h2 x).1, (h2 x).2.symm⟩⟩
  rw [e]
  have hc : ∀ x : n → ℂ, Continuous fun A : Matrix n n ℂ => star x ⬝ᵥ A *ᵥ x := fun x =>
    continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  refine (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter
    (isClosed_iInter fun x => ?_)
  exact (isClosed_le continuous_const (Complex.continuous_re.comp (hc x))).inter
    (isClosed_eq (Complex.continuous_im.comp (hc x)) continuous_const)

lemma p07s204_dens_closed {n : Type*} [Fintype n] :
    IsClosed {A : Matrix n n ℂ | IsDensityMatrix A} :=
  p07s204_psd_closed.inter (isClosed_eq continuous_id.matrix_trace continuous_const)

lemma p07s204_dens_compact {n : Type*} [Fintype n] [DecidableEq n] :
    IsCompact {A : Matrix n n ℂ | IsDensityMatrix A} := by
  have hbox : IsCompact (Set.univ.pi fun _ : n => Set.univ.pi fun _ : n =>
      Metric.closedBall (0 : ℂ) 1 : Set (n → n → ℂ)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hbox.of_isClosed_subset p07s204_dens_closed ?_
  intro A hA
  simp only [Set.mem_pi, Set.mem_univ, true_implies, mem_closedBall_zero_iff]
  exact fun i j => p07s204_dens_entry hA i j

lemma p07s204_cont_kron {I J : Type*} :
    Continuous (fun p : Matrix I I ℂ × Matrix J J ℂ => Matrix.kronecker p.1 p.2) := by
  refine continuous_pi fun x => continuous_pi fun y => ?_
  exact (continuous_fst.matrix_elem x.1 y.1).mul (continuous_snd.matrix_elem x.2 y.2)

lemma p07s204_cont_pt {I J : Type*} :
    Continuous (fun X : Matrix (I × J) (I × J) ℂ => partialTransposeFirst X) :=
  continuous_pi fun x => continuous_pi fun y => continuous_id.matrix_elem (y.1, x.2) (x.1, y.2)

def p07s204_Phi {I J : Type*} (q : ℕ)
    (p : (Fin q → ℝ) × ((Fin q → Matrix I I ℂ) × (Fin q → Matrix J J ℂ))) :
    Matrix (I × J) (I × J) ℂ :=
  ∑ k, ((p.1 k : ℝ) : ℂ) • Matrix.kronecker (p.2.1 k) (p.2.2 k)

lemma p07s204_Phi_cont {I J : Type*} (q : ℕ) : Continuous (p07s204_Phi (I := I) (J := J) q) := by
  unfold p07s204_Phi
  refine continuous_finset_sum _ fun k _ => ?_
  have h1 : Continuous fun p : (Fin q → ℝ) × ((Fin q → Matrix I I ℂ) × (Fin q → Matrix J J ℂ)) =>
      (p.2.1 k, p.2.2 k) :=
    ((continuous_apply k).comp (continuous_fst.comp continuous_snd)).prodMk
      ((continuous_apply k).comp (continuous_snd.comp continuous_snd))
  have hk := p07s204_cont_kron.comp h1
  exact (Complex.continuous_ofReal.comp ((continuous_apply k).comp continuous_fst)).smul hk

def p07s204_Kq {I J : Type*} [Fintype I] [Fintype J] (q : ℕ) : Set (Matrix (I × J) (I × J) ℂ) :=
  p07s204_Phi q '' (stdSimplex ℝ (Fin q) ×ˢ ((Set.univ.pi fun _ => {A | IsDensityMatrix A}) ×ˢ
    (Set.univ.pi fun _ => {B | IsDensityMatrix B})))

lemma p07s204_Kq_compact {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (q : ℕ) : IsCompact (p07s204_Kq (I := I) (J := J) q) :=
  ((isCompact_stdSimplex ℝ (Fin q)).prod ((isCompact_univ_pi fun _ => p07s204_dens_compact).prod
    (isCompact_univ_pi fun _ => p07s204_dens_compact))).image (p07s204_Phi_cont q)

lemma p07s204_Kq_sep {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] (q : ℕ)
    {X : Matrix (I × J) (I × J) ℂ} (hX : X ∈ p07s204_Kq q) : IsSeparableDensity X := by
  obtain ⟨⟨w, A, B⟩, ⟨hw, hA, hB⟩, rfl⟩ := hX
  exact ⟨q, w, A, B, hw.1, hw.2, fun j => ⟨hA j trivial, hB j trivial⟩, rfl⟩

lemma p07s204_sep_Kq {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    {X : Matrix (I × J) (I × J) ℂ} (hX : IsSeparableDensity X) :
    ∃ q ≤ Module.finrank ℝ (Matrix (I × J) (I × J) ℂ) + 1, X ∈ p07s204_Kq q := by
  set Pr : Set (Matrix (I × J) (I × J) ℂ) :=
    {Z | ∃ A B, IsDensityMatrix A ∧ IsDensityMatrix B ∧ Z = Matrix.kronecker A B}
  have hmem : X ∈ convexHull ℝ Pr := by
    obtain ⟨q, w, A, B, hw, hw1, hAB, rfl⟩ := hX
    simp only [Complex.coe_smul]
    exact (convex_convexHull ℝ Pr).sum_mem (fun j _ => hw j) hw1
      (fun j _ => subset_convexHull ℝ Pr ⟨A j, B j, (hAB j).1, (hAB j).2, rfl⟩)
  obtain ⟨ι, _, z, w, hz, hai, hw, hw1, hX⟩ := eq_pos_convex_span_of_mem_convexHull hmem
  have hcard : Fintype.card ι ≤ Module.finrank ℝ (Matrix (I × J) (I × J) ℂ) + 1 :=
    hai.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  have hzP : ∀ i, z i ∈ Pr := fun i => hz ⟨i, rfl⟩
  choose A B hA hB hzAB using hzP
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, hcard, ⟨(fun k => w (e.symm k), fun k => A (e.symm k),
    fun k => B (e.symm k)), ⟨⟨fun k => (hw _).le, ?_⟩, fun k _ => hA _, fun k _ => hB _⟩, ?_⟩⟩
  · rw [Equiv.sum_comp e.symm w, hw1]
  · rw [← hX]
    unfold p07s204_Phi
    simp only [Complex.coe_smul]
    rw [Equiv.sum_comp e.symm (fun i => w i • Matrix.kronecker (A i) (B i))]
    exact Finset.sum_congr rfl fun i _ => by rw [hzAB i]

lemma p07s204_sep_closed {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J] :
    IsClosed (separableBase : Set (Matrix (I × J) (I × J) ℂ)) := by
  have e : (separableBase : Set (Matrix (I × J) (I × J) ℂ)) =
      ⋃ q ∈ Finset.range (Module.finrank ℝ (Matrix (I × J) (I × J) ℂ) + 2), p07s204_Kq q := by
    ext X
    simp only [Set.mem_iUnion, Finset.mem_range]
    constructor
    · intro hX
      obtain ⟨q, hq, hXq⟩ := p07s204_sep_Kq hX
      exact ⟨q, by omega, hXq⟩
    · rintro ⟨q, -, hXq⟩
      exact p07s204_Kq_sep q hXq
  rw [e]
  exact (Finset.isCompact_biUnion _ fun q _ => p07s204_Kq_compact q).isClosed

lemma p07s204_ppt_closed {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] :
    IsClosed (pptBase : Set (Matrix (I × J) (I × J) ℂ)) :=
  p07s204_dens_closed.inter (p07s204_psd_closed.preimage p07s204_cont_pt)

lemma p07s204_rob0 {n : Type*} [Fintype n] [DecidableEq n] (S : Set (Matrix n n ℂ))
    (hS : IsClosed S) (hSd : ∀ s ∈ S, IsDensityMatrix s) {rho : Matrix n n ℂ}
    (hrho : IsDensityMatrix rho)
    (hne : {v | ∃ ap am rp rm, BaseDecomposition S rho ap am rp rm ∧ v = am}.Nonempty)
    (h0 : baseNeg S rho = 0) : rho ∈ S := by
  have hlt : ∀ k : ℕ, ∃ v ∈ {v | ∃ ap am rp rm, BaseDecomposition S rho ap am rp rm ∧ v = am},
      v < 1 / ((k : ℝ) + 1) := fun k =>
    exists_lt_of_csInf_lt hne (by unfold baseNeg at h0; rw [h0]; positivity)
  choose v hv hvl using hlt
  choose ap am rp rm hd hveq using hv
  have key : ∀ k i j, ‖rp k i j - rho i j‖ ≤ 2 * (1 / ((k : ℝ) + 1)) := by
    intro k i j
    obtain ⟨hap, ham, hrp, hrm, he⟩ := hd k
    have htr : ap k = 1 + am k := by
      have h := congrArg Matrix.trace he
      rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, hrho.2, (hSd _ hrp).2,
        (hSd _ hrm).2] at h
      have h' : ((ap k : ℝ) : ℂ) = ((1 + am k : ℝ) : ℂ) := by
        push_cast; simp at h; linear_combination -h
      exact_mod_cast h'
    have hentry := congrFun (congrFun he i) j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hentry
    have hap0 : ((1 + am k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1 + am k) ≠ 0)
    have e : rp k i j - rho i j = ((am k / ap k : ℝ) : ℂ) * (rm k i j - rho i j) := by
      rw [htr] at hentry ⊢
      rw [Complex.ofReal_div, div_mul_eq_mul_div, eq_div_iff hap0]
      push_cast at hentry ⊢
      linear_combination (-1 : ℂ) * hentry
    have hq : am k / ap k ≤ am k := by
      rw [htr]; exact div_le_self ham (by linarith)
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg ham (by rw [htr]; linarith))]
    have hb : ‖rm k i j - rho i j‖ ≤ 2 := (norm_sub_le _ _).trans (by
      linarith [p07s204_dens_entry (hSd _ hrm) i j, p07s204_dens_entry hrho i j])
    have hv' : am k < 1 / ((k : ℝ) + 1) := hveq k ▸ hvl k
    calc am k / ap k * ‖rm k i j - rho i j‖ ≤ am k * 2 :=
          mul_le_mul hq hb (norm_nonneg _) ham
      _ ≤ 2 * (1 / ((k : ℝ) + 1)) := by linarith
  have hlim : Filter.Tendsto (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1))) Filter.atTop (nhds 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
  have htend : Filter.Tendsto rp Filter.atTop (nhds rho) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    exact tendsto_iff_norm_sub_tendsto_zero.2
      (squeeze_zero (fun _ => norm_nonneg _) (fun k => key k i j) hlim)
  exact hS.mem_of_tendsto htend (Filter.Eventually.of_forall fun k => (hd k).2.2.1)

open QAlgorithms QAlgorithms.Entanglement QAlgorithms.Papers.Independent.Independent1.P07 in
theorem solution {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] [DecidableEq I] [DecidableEq J]
    (rho : Matrix (I × J) (I × J) ℂ) (hrho : IsDensityMatrix rho) :
    0 ≤ negativity rho ∧ negativity rho ≤ pptRobustness rho ∧
    pptRobustness rho ≤ separableRobustness rho ∧
    (separableRobustness rho = 0 ↔ IsSeparableDensity rho) ∧
    (pptRobustness rho = 0 ↔ (partialTransposeFirst rho).PosSemidef) ∧
    (negativity rho = 0 ↔ (partialTransposeFirst rho).PosSemidef) := by
  have hH : (partialTransposeFirst rho).IsHermitian := p07s204_pt_herm hrho.1.1
  have htr1 : (partialTransposeFirst rho).trace.re = 1 := by
    rw [p07s204_trace_pt, hrho.2, Complex.one_re]
  obtain ⟨Pp, Nn, hP, hN, hrhoe⟩ := p07s204_sep_span hrho.1.1
  have hPp := p07s204_tr_real (p07s204_sep_psd hP)
  have hNp := p07s204_tr_real (p07s204_sep_psd hN)
  have hVsep : {v | ∃ ap am rp rm, BaseDecomposition separableBase rho ap am rp rm ∧ v = am}.Nonempty := by
    obtain ⟨sp, hsp, hPe⟩ := p07s204_sep_norm hP
    obtain ⟨sn, hsn, hNe⟩ := p07s204_sep_norm hN
    exact ⟨_, _, _, sp, sn, ⟨hPp.1, hNp.1, hsp, hsn, by rw [hrhoe, ← hPe, ← hNe]⟩, rfl⟩
  have hVppt : {v | ∃ ap am rp rm, BaseDecomposition pptBase rho ap am rp rm ∧ v = am}.Nonempty := by
    obtain ⟨sp, hsp, hPe⟩ := p07s204_ppt_norm (p07s204_sep_ppt hP)
    obtain ⟨sn, hsn, hNe⟩ := p07s204_ppt_norm (p07s204_sep_ppt hN)
    exact ⟨_, _, _, sp, sn, ⟨hPp.1, hNp.1, hsp, hsn, by rw [hrhoe, ← hPe, ← hNe]⟩, rfl⟩
  have hsub : ∀ s ∈ (separableBase : Set (Matrix (I × J) (I × J) ℂ)), s ∈ pptBase := by
    rintro s ⟨q, w, A, B, hw, hw1, hAB, rfl⟩
    refine ⟨⟨Matrix.posSemidef_sum _ fun j _ => ((hAB j).1.1.kronecker (hAB j).2.1).smul
      (Complex.zero_le_real.mpr (hw j)), ?_⟩, ?_⟩
    · rw [Matrix.trace_sum]
      simp only [Matrix.trace_smul, Matrix.kronecker, Matrix.trace_kronecker, (hAB _).1.2,
        (hAB _).2.2, mul_one, smul_eq_mul]
      rw [← Complex.ofReal_sum, hw1]; simp
    · rw [p07s204_pt_sum]
      exact Matrix.posSemidef_sum _ fun j _ => by
        rw [p07s204_pt_smul, p07s204_pt_kron]
        exact ((hAB j).1.1.transpose.kronecker (hAB j).2.1).smul (Complex.zero_le_real.mpr (hw j))
  have hbdd : ∀ S : Set (Matrix (I × J) (I × J) ℂ),
      BddBelow {v | ∃ ap am rp rm, BaseDecomposition S rho ap am rp rm ∧ v = am} := fun S =>
    ⟨0, fun v hv => by obtain ⟨_, am, _, _, hd, rfl⟩ := hv; exact hd.2.1⟩
  have hnonneg : ∀ S : Set (Matrix (I × J) (I × J) ℂ), 0 ≤ baseNeg S rho := fun S =>
    Real.sInf_nonneg fun v hv => by obtain ⟨_, am, _, _, hd, rfl⟩ := hv; exact hd.2.1
  have hzero : ∀ S : Set (Matrix (I × J) (I × J) ℂ), rho ∈ S → baseNeg S rho = 0 := fun S hS =>
    le_antisymm (csInf_le (hbdd S) ⟨1, 0, rho, rho, ⟨zero_le_one, le_rfl, hS, hS, by simp⟩, rfl⟩)
      (hnonneg S)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := p07s204_re_le_tn hH
    unfold negativity; linarith
  · unfold pptRobustness baseNeg
    refine le_csInf hVppt ?_
    rintro v ⟨ap, am, rp, rm, ⟨hap, ham, hrp, hrm, he⟩, hv⟩
    rw [hv]
    have hG : partialTransposeFirst rho =
        (ap : ℂ) • partialTransposeFirst rp - (am : ℂ) • partialTransposeFirst rm := by
      rw [he, p07s204_pt_sub, p07s204_pt_smul, p07s204_pt_smul]
    have h1 := p07s204_tn_sub_le (hrp.2.smul (Complex.zero_le_real.mpr hap))
      (hrm.2.smul (Complex.zero_le_real.mpr ham))
    rw [← hG, Matrix.trace_smul, Matrix.trace_smul, p07s204_trace_pt, p07s204_trace_pt,
      hrp.1.2, hrm.1.2] at h1
    simp at h1
    have h2 := congrArg (fun X => X.trace.re) hG
    simp only [htr1, Matrix.trace_sub, Matrix.trace_smul, p07s204_trace_pt, hrp.1.2, hrm.1.2] at h2
    simp at h2
    have h3 : rho.trace.re = 1 := by rw [hrho.2]; simp
    unfold negativity; linarith
  · unfold pptRobustness separableRobustness baseNeg
    refine csInf_le_csInf (hbdd _) hVsep ?_
    rintro v ⟨ap, am, rp, rm, ⟨hap, ham, hrp, hrm, he⟩, hv⟩
    exact ⟨ap, am, rp, rm, ⟨hap, ham, hsub rp hrp, hsub rm hrm, he⟩, hv⟩
  · constructor
    · intro h
      exact p07s204_rob0 separableBase p07s204_sep_closed (fun s hs => (hsub s hs).1) hrho hVsep h
    · intro h; exact hzero _ h
  · constructor
    · intro h
      exact (p07s204_rob0 pptBase p07s204_ppt_closed (fun s hs => hs.1) hrho hVppt h).2
    · intro h; exact hzero _ ⟨hrho, h⟩
  · constructor
    · intro h0
      set H := partialTransposeFirst rho
      have hPs := p07s204_cfc_psd H (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
      have hQs := p07s204_cfc_psd H (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
      have eH := p07s204_parts H hH
      have hn := p07s204_traceNorm_herm hH
      have ht := congrArg (fun X => X.trace.re) eH
      simp only [Matrix.trace_sub, Complex.sub_re, htr1] at ht
      have hq0 : (cfc (fun t : ℝ => max (-t) 0) H).trace.re = 0 := by
        unfold negativity at h0; linarith
      have hQ0 : cfc (fun t : ℝ => max (-t) 0) H = 0 := by
        apply hQs.trace_eq_zero_iff.mp
        rw [(p07s204_tr_real hQs).2, hq0]; simp
      rw [← eH, hQ0, sub_zero]; exact hPs
    · intro h
      unfold negativity
      rw [p07s204_tn_psd h, htr1]; ring
