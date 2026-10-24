-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P03.concurrenceLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T16:19:35.482693+00:00
-- url     : https://prove2.me/submissions/ede62361-ba09-4e7a-ac77-4ae116b9565c

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03
import Mathlib

-- ===== NNA =====

/-! Generic rectangular nuclear-norm lemmas (trace of `cfc Real.sqrt (Aᴴ * A)`). -/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false

namespace X4NN

/-- rectangular nuclear norm (same formula as the target's `nuclearNorm`). -/
def nn {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J] (A : Matrix I J ℂ) : ℝ :=
  (cfc Real.sqrt (Aᴴ * A)).trace.re

lemma cont {X : Type*} [Fintype X] [DecidableEq X] (f : ℝ → ℝ) (A : Matrix X X ℂ) :
    ContinuousOn f (spectrum ℝ A) :=
  (Matrix.finite_real_spectrum (A := A)).continuousOn f

lemma sqrt_unique {X : Type*} [Fintype X] [DecidableEq X] {B S : Matrix X X ℂ}
    (hS : S.PosSemidef) (h : S * S = B) : cfc Real.sqrt B = S := by
  have hB : B.PosSemidef := by
    rw [← h]; nth_rewrite 1 [← hS.isHermitian.eq]
    exact Matrix.posSemidef_conjTranspose_mul_self S
  have := (CFC.sqrt_eq_iff B S hB.nonneg hS.nonneg).mpr h
  rw [CFC.sqrt_eq_real_sqrt B hB.nonneg, cfcₙ_eq_cfc] at this
  exact this

lemma sqrt_psd {X : Type*} [Fintype X] [DecidableEq X] (B : Matrix X X ℂ) :
    (cfc Real.sqrt B).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => Real.sqrt_nonneg t)

lemma sqrt_mul {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℂ) (hP : P.PosSemidef) :
    cfc Real.sqrt P * cfc Real.sqrt P = P := by
  have h0 : 0 ≤ P := hP.nonneg
  rw [← cfc_mul (hf := cont _ P) (hg := cont _ P)]
  conv_rhs => rw [← cfc_id' ℝ P]
  exact cfc_congr fun x hx => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg h0 hx)

lemma cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma conj_eig {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
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

/-- `tr √(A Aᴴ) = tr √(Aᴴ A)` for rectangular `A`. -/
theorem trace_sqrt_comm {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix I J ℂ) :
    (cfc Real.sqrt (A * Aᴴ)).trace = (cfc Real.sqrt (Aᴴ * A)).trace := by
  have hH : (Aᴴ * A).IsHermitian := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian
  have hpos := (Matrix.posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg
  set U : Matrix J J ℂ := (hH.eigenvectorUnitary : Matrix J J ℂ) with hU
  set lam := hH.eigenvalues with hlam
  have hD : star U * (Aᴴ * A) * U = Matrix.diagonal (RCLike.ofReal ∘ lam) := conj_eig hH
  have huu : U * star U = 1 := Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  set C : Matrix I J ℂ := A * U with hC
  have hCC : Cᴴ * C = Matrix.diagonal (RCLike.ofReal ∘ lam) := by
    rw [hC, Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose U, ← hD]
    simp only [Matrix.mul_assoc]
  set E : Matrix J J ℂ := Matrix.diagonal (fun j => (((Real.sqrt (lam j))⁻¹ : ℝ) : ℂ)) with hE
  have hEpsd : E.PosSemidef := by
    rw [hE, Matrix.posSemidef_diagonal_iff]
    intro j
    exact Complex.zero_le_real.mpr (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hEh : Eᴴ = E := hEpsd.isHermitian.eq
  set S : Matrix I I ℂ := C * E * Cᴴ with hS
  have hSpsd : S.PosSemidef := hEpsd.mul_mul_conjTranspose_same C
  -- columns of `C` with zero eigenvalue vanish
  have hcol : ∀ i j, lam j = 0 → C i j = 0 := by
    intro i j hj
    have h1 := congrArg (fun M => M j j) hCC
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq,
      Function.comp, hj] at h1
    have h2 : ∑ x, Complex.normSq (C x j) = 0 := by
      have := congrArg Complex.re h1
      simpa [Complex.mul_re, Complex.normSq_apply, mul_comm] using this
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Complex.normSq_nonneg (C x j))).1 h2 i
      (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 this
  have hCF : C * (E * Matrix.diagonal (RCLike.ofReal ∘ lam) * E) = C := by
    rw [hE, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    rw [Matrix.mul_diagonal]
    by_cases hj : lam j = 0
    · simp [hcol i j hj]
    · have hp : 0 < lam j := lt_of_le_of_ne (hpos j) (Ne.symm hj)
      have hs : 0 < Real.sqrt (lam j) := Real.sqrt_pos.2 hp
      have hr : (Real.sqrt (lam j))⁻¹ * lam j * (Real.sqrt (lam j))⁻¹ = 1 := by
        have hsq := Real.mul_self_sqrt (hpos j)
        have := hs.ne'
        field_simp
        nlinarith [hsq]
      have e : ((((Real.sqrt (lam j))⁻¹ * lam j * (Real.sqrt (lam j))⁻¹ : ℝ)) : ℂ) = 1 := by
        rw [hr]; simp
      simp only [Function.comp]
      push_cast at e ⊢
      calc _ = C i j * 1 := by congr 1
        _ = C i j := mul_one _
  have hSS : S * S = A * Aᴴ := by
    have : S * S = C * (E * (Cᴴ * C) * E) * Cᴴ := by
      rw [hS]; simp only [Matrix.mul_assoc]
    rw [this, hCC, hCF, hC, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U,
      ← Matrix.star_eq_conjTranspose U, huu, Matrix.one_mul]
  rw [sqrt_unique hSpsd hSS, cfc_trace hH, hS, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hCC,
    Matrix.trace_mul_comm, hE, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.comp]
  have key : (Real.sqrt (lam j))⁻¹ * lam j = Real.sqrt (lam j) := by
    rcases (hpos j).eq_or_lt with h | h
    · rw [← h]; simp
    · have hs : 0 < Real.sqrt (lam j) := Real.sqrt_pos.2 h
      have hsq := Real.mul_self_sqrt (hpos j)
      have := hs.ne'
      field_simp
      nlinarith [hsq]
  calc _ = (((Real.sqrt (lam j))⁻¹ * lam j : ℝ) : ℂ) := by push_cast; rfl
    _ = _ := by rw [key]

end X4NN

-- ===== NNB =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace X4NN

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J]
  [DecidableEq K]

lemma sqrt_herm {X : Type*} [Fintype X] [DecidableEq X] (B : Matrix X X ℂ) :
    (cfc Real.sqrt B)ᴴ = cfc Real.sqrt B := (sqrt_psd B).isHermitian.eq

theorem nn_ct (A : Matrix I J ℂ) : nn Aᴴ = nn A := by
  unfold nn
  rw [Matrix.conjTranspose_conjTranspose, trace_sqrt_comm]

theorem nn_comm (A : Matrix I J ℂ) : nn A = (cfc Real.sqrt (A * Aᴴ)).trace.re := by
  unfold nn; rw [trace_sqrt_comm]

/-- nuclear norm of `X Wᴴ` depends only on the two Gram matrices. -/
theorem nn_gram (X : Matrix I K ℂ) (W : Matrix J K ℂ) :
    nn (X * Wᴴ) = nn (cfc Real.sqrt (Xᴴ * X) * cfc Real.sqrt (Wᴴ * W)) := by
  set g := cfc Real.sqrt (Xᴴ * X) with hg
  set h := cfc Real.sqrt (Wᴴ * W) with hh
  have hgg : g * g = Xᴴ * X := sqrt_mul _ (Matrix.posSemidef_conjTranspose_mul_self X)
  have hhh : h * h = Wᴴ * W := sqrt_mul _ (Matrix.posSemidef_conjTranspose_mul_self W)
  have hgH : gᴴ = g := sqrt_herm _
  have hhH : hᴴ = h := sqrt_herm _
  have e1 : (X * Wᴴ)ᴴ * (X * Wᴴ) = (W * g) * (W * g)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hgH, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc g, hgg]
    simp only [Matrix.mul_assoc]
  have e2 : (W * g)ᴴ * (W * g) = (g * h) * (g * h)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hgH, hhH, Matrix.mul_assoc,
      ← Matrix.mul_assoc Wᴴ, ← hhh]
    simp only [Matrix.mul_assoc]
  unfold nn
  rw [e1, trace_sqrt_comm, e2, trace_sqrt_comm]

theorem nn_smul (w : ℝ) (hw : 0 ≤ w) (A : Matrix I J ℂ) : nn ((w : ℂ) • A) = w * nn A := by
  unfold nn
  have hpsd := Matrix.posSemidef_conjTranspose_mul_self A
  have hs : ((w : ℂ) • cfc Real.sqrt (Aᴴ * A)).PosSemidef :=
    (sqrt_psd _).smul (Complex.zero_le_real.mpr hw)
  have e : ((w : ℂ) • cfc Real.sqrt (Aᴴ * A)) * ((w : ℂ) • cfc Real.sqrt (Aᴴ * A)) =
      ((w : ℂ) • A)ᴴ * ((w : ℂ) • A) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, sqrt_mul _ hpsd, Matrix.conjTranspose_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
    congr 1
    simp [Complex.conj_ofReal]
  rw [sqrt_unique hs e, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

theorem nn_zero : nn (0 : Matrix I J ℂ) = 0 := by
  unfold nn
  rw [Matrix.conjTranspose_zero, Matrix.zero_mul,
    sqrt_unique (Matrix.PosSemidef.zero) (Matrix.zero_mul 0)]
  simp

/-- Hermitian dilation. -/
def dil (A : Matrix I J ℂ) : Matrix (I ⊕ J) (I ⊕ J) ℂ := Matrix.fromBlocks 0 A Aᴴ 0

lemma dil_herm (A : Matrix I J ℂ) : (dil A)ᴴ = dil A := by
  simp [dil, Matrix.fromBlocks_conjTranspose]

lemma dil_add (A B : Matrix I J ℂ) : dil (A + B) = dil A + dil B := by
  simp [dil, Matrix.fromBlocks_add]

/-- square trace norm -/
def tn {X : Type*} [Fintype X] [DecidableEq X] (M : Matrix X X ℂ) : ℝ :=
  (cfc Real.sqrt (Mᴴ * M)).trace.re

theorem tn_dil (A : Matrix I J ℂ) : tn (dil A) = 2 * nn A := by
  unfold tn
  set s1 := cfc Real.sqrt (A * Aᴴ)
  set s2 := cfc Real.sqrt (Aᴴ * A)
  have h1 := sqrt_psd (A * Aᴴ)
  have h2 := sqrt_psd (Aᴴ * A)
  set t1 := cfc Real.sqrt s1
  set t2 := cfc Real.sqrt s2
  have ht1 : t1 * t1 = s1 := sqrt_mul _ h1
  have ht2 : t2 * t2 = s2 := sqrt_mul _ h2
  have hS : (Matrix.fromBlocks s1 0 0 s2 : Matrix (I ⊕ J) (I ⊕ J) ℂ).PosSemidef := by
    have : (Matrix.fromBlocks s1 0 0 s2 : Matrix (I ⊕ J) (I ⊕ J) ℂ) =
        (Matrix.fromBlocks t1 0 0 t2)ᴴ * Matrix.fromBlocks t1 0 0 t2 := by
      rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, sqrt_herm, sqrt_herm, ht1,
        ht2]
      simp
    rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _
  have e : (Matrix.fromBlocks s1 0 0 s2 : Matrix (I ⊕ J) (I ⊕ J) ℂ) *
      Matrix.fromBlocks s1 0 0 s2 = (dil A)ᴴ * dil A := by
    rw [dil_herm, dil, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
      sqrt_mul _ (Matrix.posSemidef_self_mul_conjTranspose A),
      sqrt_mul _ (Matrix.posSemidef_conjTranspose_mul_self A)]
    simp
  rw [sqrt_unique hS e, nn_comm]
  have : (Matrix.fromBlocks s1 0 0 s2 : Matrix (I ⊕ J) (I ⊕ J) ℂ).trace = s1.trace + s2.trace := by
    simp [Matrix.trace, Fintype.sum_sum_type]
  rw [this, Complex.add_re, trace_sqrt_comm]
  ring

end X4NN

-- ===== NNC =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace X4NN

lemma h_posPart_aux {n : Type*} [Fintype n] [DecidableEq n] {A B U : Matrix n n ℂ} (lam : n → ℝ)
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

lemma h_parts {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma h_cfc_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma h_posPart_le {n : Type*} [Fintype n] [DecidableEq n] {Y A B : Matrix n n ℂ} (hY : Y.IsHermitian)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hYAB : Y = A - B) :
    (cfc (fun t : ℝ => max t 0) Y).trace.re ≤ A.trace.re := by
  rw [cfc_trace hY, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hD := conj_eig hY
  have hu := Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize hY.eigenvalues = lam at *
  subst hYAB
  exact h_posPart_aux lam hA hB hu hD

lemma h_traceNorm_herm {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    tn X =
      (cfc (fun t : ℝ => max t 0) X).trace.re + (cfc (fun t : ℝ => max (-t) 0) X).trace.re := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  unfold tn
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

lemma h_negPart_eq {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc (fun t : ℝ => max (-t) 0) X = cfc (fun t : ℝ => max t 0) (-X) := by
  by_cases hX : IsSelfAdjoint X
  · exact cfc_comp_neg (f := fun t : ℝ => max t 0) (a := X)
  · have : ¬ IsSelfAdjoint (-X) := fun h => hX (by simpa using h.neg)
    rw [cfc_apply_of_not_predicate X hX, cfc_apply_of_not_predicate (-X) this]

/-- trace-norm triangle inequality for Hermitian matrices -/
lemma h_traceNorm_add_le {n : Type*} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    tn (X + Y) ≤ tn X + tn Y := by
  have hXY : (X + Y).IsHermitian := hX.add hY
  rw [h_traceNorm_herm hXY, h_traceNorm_herm hX, h_traceNorm_herm hY]
  have pX := h_cfc_psd X (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have mX := h_cfc_psd X (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have pY := h_cfc_psd Y (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have mY := h_cfc_psd Y (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have eX := h_parts X hX
  have eY := h_parts Y hY
  have e1 : X + Y = (cfc (fun t : ℝ => max t 0) X + cfc (fun t : ℝ => max t 0) Y) -
      (cfc (fun t : ℝ => max (-t) 0) X + cfc (fun t : ℝ => max (-t) 0) Y) := by
    conv_lhs => rw [← eX, ← eY]
    abel
  have e2 : -(X + Y) = (cfc (fun t : ℝ => max (-t) 0) X + cfc (fun t : ℝ => max (-t) 0) Y) -
      (cfc (fun t : ℝ => max t 0) X + cfc (fun t : ℝ => max t 0) Y) := by
    rw [e1]; abel
  have h1 := h_posPart_le hXY (pX.add pY) (mX.add mY) e1
  have h2 := h_posPart_le hXY.neg (mX.add mY) (pX.add pY) e2
  rw [← h_negPart_eq] at h2
  rw [Matrix.trace_add, Complex.add_re] at h1 h2
  linarith


variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem nn_add (A B : Matrix I J ℂ) : nn (A + B) ≤ nn A + nn B := by
  have h := h_traceNorm_add_le (X := dil A) (Y := dil B) (dil_herm A) (dil_herm B)
  rw [← dil_add, tn_dil, tn_dil, tn_dil] at h
  linarith

theorem nn_nonneg (A : Matrix I J ℂ) : 0 ≤ nn A := by
  unfold nn
  exact (Complex.nonneg_iff.mp ((sqrt_psd _).trace_nonneg)).1

theorem nn_sum {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ j ∈ s, 0 ≤ w j)
    (A : ι → Matrix I J ℂ) : nn (∑ j ∈ s, (w j : ℂ) • A j) ≤ ∑ j ∈ s, w j * nn (A j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nn_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := nn_add ((w a : ℂ) • A a) (∑ j ∈ s, (w j : ℂ) • A j)
    rw [nn_smul _ (hw a (Finset.mem_insert_self a s))] at h1
    have h2 := ih (fun j hj => hw j (Finset.mem_insert_of_mem hj))
    linarith

end X4NN

-- ===== NNP =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace X4NN

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P03

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J]
  [DecidableEq K]

lemma nuclear_eq {A : Matrix I J ℂ} : nuclearNorm A = nn A := rfl

/-- stacked factor `[P ; v νᵀ]`. -/
def Xm {m r : ℕ} {α : Type*} (P : Matrix (Fin m) (Fin r) ℝ) (nu : Fin r → ℝ) (v : α → ℂ) :
    Matrix (Fin m ⊕ α) (Fin r) ℂ :=
  Matrix.fromRows (fun i k => (P i k : ℂ)) (fun a k => v a * (nu k : ℂ))

lemma Xm_gram {m r : ℕ} {α : Type*} [Fintype α] (P : Matrix (Fin m) (Fin r) ℝ) (nu : Fin r → ℝ)
    (v : α → ℂ) (hv : ∑ a, Complex.normSq (v a) = 1) :
    (Xm P nu v)ᴴ * Xm P nu v = augmentedGram P nu := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Xm, Fintype.sum_sum_type,
    Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, augmentedGram]
  have h2 : ∑ x, star (v x * (nu i : ℂ)) * (v x * (nu j : ℂ)) =
      ((nu i * nu j : ℝ) : ℂ) * ∑ x, ((Complex.normSq (v x) : ℝ) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
    push_cast; ring
  rw [h2, ← Complex.ofReal_sum, hv]
  push_cast
  simp [Complex.conj_ofReal]

lemma Xm_conv {m r : ℕ} {α : Type*} (P : Matrix (Fin m) (Fin r) ℝ) (nu : Fin r → ℝ)
    (v : α → ℂ) (s : ℝ) (hs : s ≠ 0) :
    Xm P nu v = (((1 + s) / 2 : ℝ) : ℂ) • Xm P nu (fun a => v a / s) +
      ((1 - (1 + s) / 2 : ℝ) : ℂ) • Xm P nu (fun a => -(v a / s)) := by
  have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  ext p k
  rcases p with i | a
  · simp only [Xm, Matrix.add_apply, Matrix.smul_apply, Matrix.fromRows_apply_inl, smul_eq_mul]
    push_cast; ring
  · simp only [Xm, Matrix.add_apply, Matrix.smul_apply, Matrix.fromRows_apply_inr, smul_eq_mul]
    push_cast; field_simp; ring

lemma conv4 (X1 X2 : Matrix I K ℂ) (Y1 Y2 : Matrix J K ℂ) (a b M : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (h11 : nn (X1 * Y1ᴴ) ≤ M) (h12 : nn (X1 * Y2ᴴ) ≤ M) (h21 : nn (X2 * Y1ᴴ) ≤ M)
    (h22 : nn (X2 * Y2ᴴ) ≤ M) :
    nn (((a : ℂ) • X1 + ((1 - a : ℝ) : ℂ) • X2) * ((b : ℂ) • Y1 + ((1 - b : ℝ) : ℂ) • Y2)ᴴ) ≤ M := by
  have e : ((a : ℂ) • X1 + ((1 - a : ℝ) : ℂ) • X2) * ((b : ℂ) • Y1 + ((1 - b : ℝ) : ℂ) • Y2)ᴴ =
      ((a * b : ℝ) : ℂ) • (X1 * Y1ᴴ) + ((a * (1 - b) : ℝ) : ℂ) • (X1 * Y2ᴴ) +
      (((1 - a) * b : ℝ) : ℂ) • (X2 * Y1ᴴ) + (((1 - a) * (1 - b) : ℝ) : ℂ) • (X2 * Y2ᴴ) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def,
      Complex.conj_ofReal]
    push_cast
    module
  rw [e]
  have k1 := nn_add (((a * b : ℝ) : ℂ) • (X1 * Y1ᴴ) + ((a * (1 - b) : ℝ) : ℂ) • (X1 * Y2ᴴ) +
      (((1 - a) * b : ℝ) : ℂ) • (X2 * Y1ᴴ)) ((((1 - a) * (1 - b) : ℝ) : ℂ) • (X2 * Y2ᴴ))
  have k2 := nn_add (((a * b : ℝ) : ℂ) • (X1 * Y1ᴴ) + ((a * (1 - b) : ℝ) : ℂ) • (X1 * Y2ᴴ))
      ((((1 - a) * b : ℝ) : ℂ) • (X2 * Y1ᴴ))
  have k3 := nn_add (((a * b : ℝ) : ℂ) • (X1 * Y1ᴴ)) (((a * (1 - b) : ℝ) : ℂ) • (X1 * Y2ᴴ))
  have p1 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have p2 : 0 ≤ a * (1 - b) := mul_nonneg ha0 (by linarith)
  have p3 : 0 ≤ (1 - a) * b := mul_nonneg (by linarith) hb0
  have p4 : 0 ≤ (1 - a) * (1 - b) := mul_nonneg (by linarith) (by linarith)
  rw [nn_smul _ p1] at k3
  rw [nn_smul _ p2] at k3
  rw [nn_smul _ p3] at k2
  rw [nn_smul _ p4] at k1
  have := mul_le_mul_of_nonneg_left h11 p1
  have := mul_le_mul_of_nonneg_left h12 p2
  have := mul_le_mul_of_nonneg_left h21 p3
  have := mul_le_mul_of_nonneg_left h22 p4
  nlinarith


lemma normSq_div_sum {α : Type*} [Fintype α] (v : α → ℂ) (s : ℝ) (hs : 0 < s)
    (ht : ∑ a, Complex.normSq (v a) = s ^ 2) (sgn : ℂ) (hsgn : Complex.normSq sgn = 1) :
    ∑ a, Complex.normSq (sgn * (v a / s)) = 1 := by
  simp only [Complex.normSq_mul, Complex.normSq_div, Complex.normSq_ofReal, hsgn, one_mul]
  rw [← Finset.sum_div, ht]
  field_simp

lemma unit_bound {m n r : ℕ} {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (z : Parameters m n r) (v : α → ℂ) (w : β → ℂ)
    (hv : ∑ a, Complex.normSq (v a) = 1) (hw : ∑ a, Complex.normSq (w a) = 1) :
    nn (Xm z.P z.nu v * (Xm z.Q z.mu w)ᴴ) = separableBound z := by
  rw [nn_gram, Xm_gram _ _ _ hv, Xm_gram _ _ _ hw]
  rfl

lemma prod_bound {m n r : ℕ} {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (z : Parameters m n r) (v : α → ℂ) (w : β → ℂ)
    (hv0 : 0 < ∑ a, Complex.normSq (v a)) (hv1 : ∑ a, Complex.normSq (v a) ≤ 1)
    (hw0 : 0 < ∑ a, Complex.normSq (w a)) (hw1 : ∑ a, Complex.normSq (w a) ≤ 1) :
    nn (Xm z.P z.nu v * (Xm z.Q z.mu w)ᴴ) ≤ separableBound z := by
  set s := Real.sqrt (∑ a, Complex.normSq (v a)) with hs
  set t := Real.sqrt (∑ a, Complex.normSq (w a)) with ht
  have hs0 : 0 < s := Real.sqrt_pos.2 hv0
  have ht0 : 0 < t := Real.sqrt_pos.2 hw0
  have hs1 : s ≤ 1 := Real.sqrt_le_one.mpr hv1
  have ht1 : t ≤ 1 := Real.sqrt_le_one.mpr hw1
  have hs2 : ∑ a, Complex.normSq (v a) = s ^ 2 := (Real.sq_sqrt hv0.le).symm
  have ht2 : ∑ a, Complex.normSq (w a) = t ^ 2 := (Real.sq_sqrt hw0.le).symm
  have u1 := normSq_div_sum v s hs0 hs2 1 (by simp)
  have u2 := normSq_div_sum v s hs0 hs2 (-1) (by simp)
  have u3 := normSq_div_sum w t ht0 ht2 1 (by simp)
  have u4 := normSq_div_sum w t ht0 ht2 (-1) (by simp)
  simp only [one_mul, neg_one_mul] at u1 u2 u3 u4
  rw [Xm_conv z.P z.nu v s hs0.ne', Xm_conv z.Q z.mu w t ht0.ne']
  apply conv4 _ _ _ _ _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) <;>
    exact (unit_bound z _ _ (by assumption) (by assumption)).le

end X4NN

-- ===== NNQ =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace X4NN

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P03

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma enh_prod {m n r : ℕ} (z : Parameters m n r) (A : Matrix I I ℂ) (B : Matrix J J ℂ)
    (hA : A.trace = 1) (hB : B.trace = 1) :
    enhanced z (Matrix.kronecker A B) =
      Xm z.P z.nu (columnVec A) * (Xm z.Q z.mu (fun b => conj (columnVec B b)))ᴴ := by
  have hR : traceRight (Matrix.kronecker A B) = A := by
    ext i j
    change ∑ h, A i j * B h h = A i j
    rw [← Finset.mul_sum]
    have : ∑ h, B h h = 1 := hB
    rw [this, mul_one]
  have hL : traceLeft (Matrix.kronecker A B) = B := by
    ext i j
    change ∑ h, A h h * B i j = B i j
    rw [← Finset.sum_mul]
    have : ∑ h, A h h = 1 := hA
    rw [this, one_mul]
  have hp : ∑ k, (z.nu k : ℂ) * (z.mu k : ℂ) = 1 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) z.pairing
    push_cast at this; exact this
  ext p q
  rcases p with i | a <;> rcases q with j | b
  · simp [enhanced, Xm, Matrix.mul_apply, Complex.conj_ofReal]
  · simp only [enhanced, hL, Matrix.fromBlocks_apply₁₂, Xm, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Complex.conj_ofReal]; ring
  · simp only [enhanced, hR, Matrix.fromBlocks_apply₂₁, Xm, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Complex.conj_ofReal]; ring
  · simp only [enhanced, Matrix.fromBlocks_apply₂₂, Xm, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.fromRows_apply_inr]
    have e : ∀ k, columnVec A a * (z.nu k : ℂ) * star (conj (columnVec B b) * (z.mu k : ℂ)) =
        columnVec A a * columnVec B b * ((z.nu k : ℂ) * (z.mu k : ℂ)) := by
      intro k; simp [Complex.conj_ofReal]; ring
    simp only [e, ← Finset.mul_sum, hp, mul_one]
    rfl

lemma dens_frob (A : Matrix I I ℂ) (hA : IsDensityMatrix A) :
    0 < ∑ p : I × I, Complex.normSq (columnVec A p) ∧
      ∑ p : I × I, Complex.normSq (columnVec A p) ≤ 1 := by
  have hS : ∑ p : I × I, Complex.normSq (columnVec A p) = ∑ i, ∑ j, Complex.normSq (A i j) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]; rfl
  rw [hS]
  have hH : A.IsHermitian := hA.1.isHermitian
  have hpos := hA.1.eigenvalues_nonneg
  have htr : ∑ i, hH.eigenvalues i = 1 := by
    have := hH.trace_eq_sum_eigenvalues
    rw [hA.2] at this
    have := congrArg Complex.re this
    simpa using this.symm
  have hAA : (A * A).trace.re = ∑ i, ∑ j, Complex.normSq (A i j) := by
    have : (A * A).trace = (Aᴴ * A).trace := by rw [hH.eq]
    rw [this, Matrix.trace, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_apply]; simp [Complex.mul_re]
  have hsq : A * A = cfc (fun x : ℝ => x * x) A := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) A (cont _ A) (cont _ A), cfc_id' ℝ A]
  have hAA2 : (A * A).trace.re = ∑ i, hH.eigenvalues i * hH.eigenvalues i := by
    rw [hsq, cfc_trace hH, Complex.re_sum]; simp
  constructor
  · by_contra h
    push Not at h
    have h0 : ∑ i, ∑ j, Complex.normSq (A i j) = 0 :=
      le_antisymm h (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)
    have : ∀ i, A i i = 0 := by
      intro i
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg
        fun j _ => Complex.normSq_nonneg (A i j))).1 h0 i (Finset.mem_univ _)
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (A i j))).1 h1 i
        (Finset.mem_univ _)
      exact Complex.normSq_eq_zero.1 h2
    have h3 := hA.2
    simp [Matrix.trace, Matrix.diag, this] at h3
  · rw [← hAA, hAA2, ← htr]
    refine Finset.sum_le_sum fun i _ => ?_
    have : hH.eigenvalues i ≤ 1 := by
      rw [← htr]; exact Finset.single_le_sum (fun j _ => hpos j) (Finset.mem_univ i)
    nlinarith [hpos i]

lemma enh_affine {m n r q : ℕ} (z : Parameters m n r) (w : Fin q → ℝ) (hw : ∑ j, w j = 1)
    (ρ : Fin q → Matrix (I × J) (I × J) ℂ) :
    enhanced z (∑ j, (w j : ℂ) • ρ j) = ∑ j, (w j : ℂ) • enhanced z (ρ j) := by
  have hw' : ∑ j, (w j : ℂ) = 1 := by exact_mod_cast hw
  ext p q
  rcases p with i | a <;> rcases q with k | b
  · simp only [enhanced, Matrix.fromBlocks_apply₁₁, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul]
    rw [← Finset.sum_mul, hw', one_mul]
  · simp only [enhanced, Matrix.fromBlocks_apply₁₂, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, columnVec, traceLeft, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp only [enhanced, Matrix.fromBlocks_apply₂₁, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, columnVec, traceRight, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp [enhanced, Matrix.sum_apply, realignment]

theorem main {dA dB m n r : ℕ} [NeZero dA] [NeZero dB]
    (z : Parameters m n r)
    (rho : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hsep : Entanglement.IsSeparableDensity rho) :
    nuclearNorm (enhanced z rho) ≤ separableBound z := by
  obtain ⟨q, w, A, B, hw0, hw1, hAB, rfl⟩ := hsep
  rw [nuclear_eq, enh_affine z w hw1]
  refine (nn_sum Finset.univ w (fun j _ => hw0 j) _).trans ?_
  have : ∀ j, nn (enhanced z (Matrix.kronecker (A j) (B j))) ≤ separableBound z := by
    intro j
    obtain ⟨hA, hB⟩ := hAB j
    rw [enh_prod z (A j) (B j) hA.2 hB.2]
    obtain ⟨a0, a1⟩ := dens_frob (A j) hA
    obtain ⟨b0, b1⟩ := dens_frob (B j) hB
    apply prod_bound z _ _ a0 a1 <;> simpa [Complex.normSq_conj] using (by assumption)
  calc ∑ j, w j * nn (enhanced z (Matrix.kronecker (A j) (B j)))
      ≤ ∑ j, w j * separableBound z :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (this j) (hw0 j)
    _ = separableBound z := by rw [← Finset.sum_mul, hw1, one_mul]

end X4NN

-- ===== NNR =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace X4NN

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P03

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J]
  [DecidableEq K]

lemma star_dot {α : Type*} [Fintype α] (a : α → ℂ) :
    star a ⬝ᵥ a = ((∑ i, Complex.normSq (a i) : ℝ) : ℂ) := by
  rw [dotProduct, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]; rfl

theorem nn_rank1 (a : I → ℂ) (b : J → ℂ) :
    nn (Matrix.vecMulVec a (star b)) =
      Real.sqrt (∑ i, Complex.normSq (a i)) * Real.sqrt (∑ j, Complex.normSq (b j)) := by
  set na := Real.sqrt (∑ i, Complex.normSq (a i))
  set nb := Real.sqrt (∑ j, Complex.normSq (b j))
  have ha2 : ∑ i, Complex.normSq (a i) = na ^ 2 :=
    (Real.sq_sqrt (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)).symm
  have hb2 : ∑ j, Complex.normSq (b j) = nb ^ 2 :=
    (Real.sq_sqrt (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)).symm
  have hna : 0 ≤ na := Real.sqrt_nonneg _
  have hnb : 0 ≤ nb := Real.sqrt_nonneg _
  by_cases hb : nb = 0
  · have : b = 0 := by
      funext j
      have h0 : ∑ j, Complex.normSq (b j) = 0 := by rw [hb2, hb]; ring
      exact Complex.normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Complex.normSq_nonneg (b j))).1 h0 j (Finset.mem_univ _))
    subst this
    have h0 : Matrix.vecMulVec a (star (0 : J → ℂ)) = 0 := by
      ext i j; simp [Matrix.vecMulVec_apply]
    rw [hb, mul_zero, h0, nn_zero]
  have hnb0 : 0 < nb := lt_of_le_of_ne hnb (Ne.symm hb)
  unfold nn
  have e1 : (Matrix.vecMulVec a (star b))ᴴ * Matrix.vecMulVec a (star b) =
      ((na ^ 2 : ℝ) : ℂ) • Matrix.vecMulVec b (star b) := by
    rw [Matrix.conjTranspose_vecMulVec, Matrix.vecMulVec_mul_vecMulVec, star_star, star_dot, ha2,
      Matrix.vecMulVec_smul]
  set S : Matrix J J ℂ := ((na / nb : ℝ) : ℂ) • Matrix.vecMulVec b (star b) with hS
  have hSp : S.PosSemidef := (Matrix.posSemidef_vecMulVec_self_star b).smul
    (Complex.zero_le_real.mpr (div_nonneg hna hnb))
  have e2 : S * S = ((na ^ 2 : ℝ) : ℂ) • Matrix.vecMulVec b (star b) := by
    rw [hS, Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, star_dot, hb2,
      Matrix.vecMulVec_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    field_simp
  rw [e1, ← e2, sqrt_unique hSp rfl, hS, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have : (Matrix.vecMulVec b (star b)).trace.re = nb ^ 2 := by
    rw [Matrix.trace, Complex.re_sum, ← hb2]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.vecMulVec_apply, Complex.mul_conj]
  rw [this]
  field_simp

theorem nn_frob (A : Matrix I K ℂ) (B : Matrix J K ℂ) :
    nn (A * Bᴴ) ≤ Real.sqrt (∑ k, ∑ i, Complex.normSq (A i k)) *
      Real.sqrt (∑ k, ∑ j, Complex.normSq (B j k)) := by
  have e : A * Bᴴ = ∑ k, ((1 : ℝ) : ℂ) • Matrix.vecMulVec (fun i => A i k) (star fun j => B j k) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]
  rw [e]
  refine (nn_sum Finset.univ (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) _).trans ?_
  simp only [one_mul, nn_rank1]
  refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans_eq ?_
  congr 2 <;> refine Finset.sum_congr rfl fun k _ => Real.sq_sqrt
    (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)

lemma frob_sq {m r : ℕ} (P : Matrix (Fin m) (Fin r) ℝ) :
    frobNorm (fun i j => (P i j : ℂ)) ^ 2 = ∑ i, ∑ k, P i k ^ 2 := by
  unfold frobNorm
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (Finset.sum_nonneg
    fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Real.rpow_two, Complex.norm_real, Real.norm_eq_abs, sq_abs]

lemma gram_sq {s r : ℕ} (P : Matrix (Fin s) (Fin r) ℝ) (v : Fin r → ℝ) :
    ∑ k, ∑ i, Complex.normSq (cfc Real.sqrt (augmentedGram P v) i k) =
      ∑ i, ∑ k, P i k ^ 2 + ∑ k, v k ^ 2 := by
  set g := cfc Real.sqrt (augmentedGram P v)
  have hG : (augmentedGram P v).PosSemidef := by
    have : augmentedGram P v = (Xm P v (fun _ : Unit => (1 : ℂ)))ᴴ * Xm P v (fun _ => 1) :=
      (Xm_gram P v _ (by simp)).symm
    rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _
  have hgg : gᴴ * g = augmentedGram P v := by rw [sqrt_herm, sqrt_mul _ hG]
  have h1 : ((gᴴ * g).trace).re = ∑ k, ∑ i, Complex.normSq (g i k) := by
    rw [Matrix.trace, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_apply]; simp [Complex.mul_re]
  rw [← h1, hgg, Matrix.trace, Complex.re_sum]
  simp only [Matrix.diag, augmentedGram, Complex.ofReal_re]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp [sq]

theorem corollary {dA dB m n r : ℕ} [NeZero dA] [NeZero dB]
    (z : Parameters m n r)
    (rho : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hsep : Entanglement.IsSeparableDensity rho) :
    nuclearNorm (enhanced z rho) ≤
      Real.sqrt (frobNorm (fun i j => (z.P i j : ℂ)) ^ 2 + ∑ k, z.nu k ^ 2) *
      Real.sqrt (frobNorm (fun i j => (z.Q i j : ℂ)) ^ 2 + ∑ k, z.mu k ^ 2) := by
  refine (main z rho hsep).trans ?_
  have h := nn_frob (cfc Real.sqrt (augmentedGram z.P z.nu)) (cfc Real.sqrt (augmentedGram z.Q z.mu))
  rw [sqrt_herm, gram_sq, gram_sq] at h
  rw [frob_sq, frob_sq]
  exact h

end X4NN

-- ===== NNL =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace X4NN

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P03

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def outer {α : Type*} (x y : EuclideanSpace ℂ α) : Matrix α α ℂ :=
  Matrix.of fun i j => x i * conj (y j)

lemma colvec_normSq {α : Type*} [Fintype α] (x y : EuclideanSpace ℂ α) :
    ∑ p : α × α, Complex.normSq (columnVec (outer x y) p) =
      (∑ i, Complex.normSq (x i)) * (∑ i, Complex.normSq (y i)) := by
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [columnVec, outer, Complex.normSq_mul, Complex.normSq_conj]

lemma normSq_one {α : Type*} [Fintype α] (x : EuclideanSpace ℂ α) (hx : ‖x‖ = 1) :
    ∑ i, Complex.normSq (x i) = 1 := by
  rw [EuclideanSpace.norm_eq] at hx
  have h0 : 0 ≤ ∑ i, ‖x i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have : ∑ i, ‖x i‖ ^ 2 = 1 := by
    have := congrArg (· ^ 2) hx
    simp only [Real.sq_sqrt h0, one_pow] at this
    exact this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_norm_sq]

/-- the linear part of `enhanced`. -/
def lin {m n r : ℕ} (z : Parameters m n r) :
    Matrix (I × J) (I × J) ℂ →ₗ[ℂ] Matrix (Fin m ⊕ (I × I)) (Fin n ⊕ (J × J)) ℂ where
  toFun ρ := enhanced z ρ - enhanced z 0
  map_add' ρ σ := by
    ext p q
    rcases p with i | a <;> rcases q with j | b <;>
      simp [enhanced, traceLeft, traceRight, columnVec, realignment, Finset.sum_add_distrib] <;>
      ring
  map_smul' c ρ := by
    ext p q
    rcases p with i | a <;> rcases q with j | b <;>
      simp [enhanced, traceLeft, traceRight, columnVec, realignment, Finset.mul_sum] <;>
      simp only [Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]

lemma enh_eq {m n r : ℕ} (z : Parameters m n r) (ρ : Matrix (I × J) (I × J) ℂ) :
    enhanced z ρ = enhanced z 0 + lin z ρ := by
  simp [lin]

/-- off-diagonal rank-one block. -/
def offd (x x' : EuclideanSpace ℂ I) (y y' : EuclideanSpace ℂ J) {m n : ℕ} :
    Matrix (Fin m ⊕ (I × I)) (Fin n ⊕ (J × J)) ℂ :=
  Matrix.vecMulVec (Sum.elim 0 (columnVec (outer x x')))
    (star (Sum.elim 0 (star (columnVec (outer y y')))))

lemma lin_off {m n r : ℕ} (z : Parameters m n r) (x x' : EuclideanSpace ℂ I)
    (y y' : EuclideanSpace ℂ J) (hx : ∑ i, x i * conj (x' i) = 0)
    (hy : ∑ i, y i * conj (y' i) = 0) :
    lin z (Matrix.kronecker (outer x x') (outer y y')) = offd x x' y y' := by
  have hL : traceLeft (Matrix.kronecker (outer x x') (outer y y')) = 0 := by
    ext i j
    change ∑ h, outer x x' h h * outer y y' i j = 0
    rw [← Finset.sum_mul]
    simp only [outer, Matrix.of_apply]
    rw [hx, zero_mul]
  have hR : traceRight (Matrix.kronecker (outer x x') (outer y y')) = 0 := by
    ext i j
    change ∑ h, outer x x' i j * outer y y' h h = 0
    rw [← Finset.mul_sum]
    simp only [outer, Matrix.of_apply]
    rw [hy, mul_zero]
  ext p q
  rcases p with i | a <;> rcases q with j | b
  · simp [lin, enhanced, offd, Matrix.vecMulVec_apply]
  · simp only [lin, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sub_apply, enhanced,
      Matrix.fromBlocks_apply₁₂, hL]
    simp [offd, columnVec, traceLeft, Matrix.vecMulVec_apply]
  · simp only [lin, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sub_apply, enhanced,
      Matrix.fromBlocks_apply₂₁, hR]
    simp [offd, columnVec, traceRight, Matrix.vecMulVec_apply]
  · simp [lin, enhanced, offd, Matrix.vecMulVec_apply, realignment, columnVec]

lemma nn_offd {m n : ℕ} (x x' : EuclideanSpace ℂ I) (y y' : EuclideanSpace ℂ J)
    (hx : ‖x‖ = 1) (hx' : ‖x'‖ = 1) (hy : ‖y‖ = 1) (hy' : ‖y'‖ = 1) :
    nn (offd x x' y y' (m := m) (n := n)) = 1 := by
  rw [offd, nn_rank1]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, map_zero,
    Finset.sum_const_zero, zero_add, Pi.star_apply]
  simp only [Complex.star_def, Complex.normSq_conj, colvec_normSq, normSq_one _ hx,
    normSq_one _ hx', normSq_one _ hy, normSq_one _ hy']
  simp

end X4NN

-- ===== NNS =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace X4NN

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P03

lemma orth_sum {α ι : Type*} [Fintype α] {v : ι → EuclideanSpace ℂ α} (hv : Orthonormal ℂ v)
    {k l : ι} (hkl : k ≠ l) : ∑ i, v k i * conj (v l i) = 0 := by
  have := hv.2 hkl.symm
  simp only [PiLp.inner_apply, RCLike.inner_apply] at this
  rw [← this]

lemma phi_apply {dA dB : ℕ} (s : SchmidtData dA dB) (p : Fin dA × Fin dB) :
    schmidtVector s p = ∑ k, (Real.sqrt (s.probability k) : ℂ) * (s.left k p.1 * s.right k p.2) := by
  simp [schmidtVector, tensorVec]

lemma pure_eq {dA dB : ℕ} (s : SchmidtData dA dB) :
    pureDensity (schmidtVector s) = ∑ k, ∑ l,
      ((Real.sqrt (s.probability k) * Real.sqrt (s.probability l) : ℝ) : ℂ) •
        Matrix.kronecker (outer (s.left k) (s.left l)) (outer (s.right k) (s.right l)) := by
  ext p q
  simp only [pureDensity, Matrix.of_apply, phi_apply, map_sum, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  change _ = _ * (outer (s.left k) (s.left l) p.1 q.1 * outer (s.right k) (s.right l) p.2 q.2)
  simp [outer, Complex.conj_ofReal]
  ring

lemma decomp {dA dB m n r : ℕ} (z : Parameters m n r) (s : SchmidtData dA dB) :
    enhanced z (pureDensity (schmidtVector s)) =
      ∑ k, ((s.probability k : ℝ) : ℂ) • enhanced z
        (Matrix.kronecker (outer (s.left k) (s.left k)) (outer (s.right k) (s.right k))) +
      ∑ k, ∑ l, ((if k = l then 0 else Real.sqrt (s.probability k) * Real.sqrt (s.probability l)
        : ℝ) : ℂ) • offd (s.left k) (s.left l) (s.right k) (s.right l) := by
  have hp : ∑ k, ((s.probability k : ℝ) : ℂ) = 1 := by exact_mod_cast s.total
  rw [enh_eq, pure_eq, map_sum]
  simp only [map_sum, map_smul]
  conv_rhs => enter [1, 2, k]; rw [enh_eq, smul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul, hp, one_smul, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : ∀ l, ((Real.sqrt (s.probability k) * Real.sqrt (s.probability l) : ℝ) : ℂ) •
      lin z (Matrix.kronecker (outer (s.left k) (s.left l)) (outer (s.right k) (s.right l))) =
      (if k = l then ((s.probability k : ℝ) : ℂ) •
        lin z (Matrix.kronecker (outer (s.left k) (s.left k)) (outer (s.right k) (s.right k)))
        else 0) +
      ((if k = l then 0 else Real.sqrt (s.probability k) * Real.sqrt (s.probability l) : ℝ) : ℂ) •
        offd (s.left k) (s.left l) (s.right k) (s.right l) := by
    intro l
    by_cases h : k = l
    · subst h
      simp [Real.mul_self_sqrt (s.nonnegative k)]
    · rw [if_neg h, if_neg h, zero_add,
        lin_off z _ _ _ _ (orth_sum s.leftOrthonormal h) (orth_sum s.rightOrthonormal h)]
  simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma pair_sum {d : ℕ} (f : Fin d → Fin d → ℝ) (hf : ∀ i j, f i j = f j i) :
    ∑ k, ∑ l, (if k = l then 0 else f k l) = 2 * ∑ i, ∑ j, (if i < j then f i j else 0) := by
  have h1 : ∀ k l, (if k = l then 0 else f k l) =
      (if k < l then f k l else 0) + (if l < k then f l k else 0) := by
    intro k l
    rcases lt_trichotomy k l with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le, hf]
  simp only [h1, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun k l => if l < k then f l k else 0)]
  ring

theorem lemma2 {dA dB m n r : ℕ} [NeZero dA] [NeZero dB]
    (z : Parameters m n r) (s : SchmidtData dA dB) :
    nuclearNorm (enhanced z (pureDensity (schmidtVector s))) ≤ separableBound z +
      2 * (∑ i : Fin (min dA dB), ∑ j : Fin (min dA dB),
        if i < j then Real.sqrt (s.probability i * s.probability j) else 0) := by
  rw [nuclear_eq, decomp]
  refine (nn_add _ _).trans ?_
  have hA := s.leftOrthonormal
  have hB := s.rightOrthonormal
  have h1 : nn (∑ k, ((s.probability k : ℝ) : ℂ) • enhanced z
        (Matrix.kronecker (outer (s.left k) (s.left k)) (outer (s.right k) (s.right k)))) ≤
      separableBound z := by
    refine (nn_sum _ _ (fun k _ => s.nonnegative k) _).trans ?_
    have : ∀ k, nn (enhanced z (Matrix.kronecker (outer (s.left k) (s.left k))
        (outer (s.right k) (s.right k)))) = separableBound z := by
      intro k
      have tA : (outer (s.left k) (s.left k)).trace = 1 := by
        have := normSq_one _ (hA.1 k)
        rw [Matrix.trace]
        simp only [Matrix.diag, outer, Matrix.of_apply, Complex.mul_conj]
        exact_mod_cast this
      have tB : (outer (s.right k) (s.right k)).trace = 1 := by
        have := normSq_one _ (hB.1 k)
        rw [Matrix.trace]
        simp only [Matrix.diag, outer, Matrix.of_apply, Complex.mul_conj]
        exact_mod_cast this
      rw [enh_prod z _ _ tA tB]
      apply unit_bound
      · rw [colvec_normSq, normSq_one _ (hA.1 k), one_mul]
      · simp only [Complex.normSq_conj]
        rw [colvec_normSq, normSq_one _ (hB.1 k), one_mul]
    simp only [this]
    rw [← Finset.sum_mul, s.total, one_mul]
  have h2 : nn (∑ k, ∑ l, ((if k = l then 0 else Real.sqrt (s.probability k) *
        Real.sqrt (s.probability l) : ℝ) : ℂ) • offd (s.left k) (s.left l) (s.right k) (s.right l)
        (m := m) (n := n)) ≤
      ∑ k, ∑ l, (if k = l then 0 else Real.sqrt (s.probability k) * Real.sqrt (s.probability l)) := by
    have e : ∀ X : Fin (min dA dB) → Matrix (Fin m ⊕ (Fin dA × Fin dA)) (Fin n ⊕ (Fin dB × Fin dB)) ℂ,
        ∑ k, X k = ∑ k, ((1 : ℝ) : ℂ) • X k := fun X => by simp
    rw [e]
    refine (nn_sum _ _ (fun _ _ => zero_le_one) _).trans ?_
    simp only [one_mul]
    refine Finset.sum_le_sum fun k _ => (nn_sum _ _ (fun l _ => ?_) _).trans_eq ?_
    · split_ifs
      · exact le_rfl
      · exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · simp only [nn_offd _ _ _ _ (hA.1 _) (hA.1 _) (hB.1 _) (hB.1 _), mul_one]
  have h3 := pair_sum (fun i j => Real.sqrt (s.probability i) * Real.sqrt (s.probability j))
    (fun i j => mul_comm _ _)
  have h4 : ∀ i j, Real.sqrt (s.probability i * s.probability j) =
      Real.sqrt (s.probability i) * Real.sqrt (s.probability j) :=
    fun i j => Real.sqrt_mul (s.nonnegative i) _
  simp only [h4]
  linarith

theorem lemma2b {d : ℕ} (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (ht : ∑ i, p i = 1) :
    2 * (∑ i, ∑ j, if i < j then Real.sqrt (p i * p j) else 0) ≤ (d : ℝ) - 1 := by
  have h3 := pair_sum (fun i j => Real.sqrt (p i) * Real.sqrt (p j)) (fun i j => mul_comm _ _)
  have h4 : ∀ i j, Real.sqrt (p i * p j) = Real.sqrt (p i) * Real.sqrt (p j) :=
    fun i j => Real.sqrt_mul (hp i) _
  simp only [h4]
  rw [← h3]
  have hsq : (∑ i, Real.sqrt (p i)) ^ 2 = 1 + ∑ k, ∑ l,
      (if k = l then 0 else Real.sqrt (p k) * Real.sqrt (p l)) := by
    rw [sq, Finset.sum_mul_sum, ← ht, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : ∀ l, Real.sqrt (p k) * Real.sqrt (p l) =
        (if k = l then p k else 0) + (if k = l then 0 else Real.sqrt (p k) * Real.sqrt (p l)) := by
      intro l
      by_cases h : k = l
      · subst h; simp [Real.mul_self_sqrt (hp k)]
      · simp [h]
    rw [Finset.sum_congr rfl fun l _ => this l]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hcs : (∑ i, Real.sqrt (p i)) ^ 2 ≤ (d : ℝ) * ∑ i, p i := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin d => (1 : ℝ))
      (fun i => Real.sqrt (p i))
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at h
    have e : ∀ i, Real.sqrt (p i) ^ 2 = p i := fun i => Real.sq_sqrt (hp i)
    simp only [e] at h
    exact h
  rw [ht, mul_one] at hcs
  linarith

theorem pure_schmidt {dA dB m n r : ℕ} [NeZero dA] [NeZero dB]
    (z : Parameters m n r) (s : SchmidtData dA dB) :
    nuclearNorm (enhanced z (pureDensity (schmidtVector s))) ≤ separableBound z +
      2 * (∑ i : Fin (min dA dB), ∑ j : Fin (min dA dB),
        if i < j then Real.sqrt (s.probability i * s.probability j) else 0) ∧
    nuclearNorm (enhanced z (pureDensity (schmidtVector s))) ≤
      separableBound z + ((min dA dB : ℝ) - 1) := by
  have h1 := lemma2 z s
  refine ⟨h1, h1.trans ?_⟩
  have := lemma2b s.probability s.nonnegative s.total
  push_cast at this ⊢
  linarith

end X4NN

-- ===== NNT =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace X4NN

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P03

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- generalized Schmidt form: orthogonal left vectors, orthonormal right vectors. -/
theorem rep (φ : EuclideanSpace ℂ (I × J)) :
    ∃ x : J → EuclideanSpace ℂ I, ∃ y : J → EuclideanSpace ℂ J,
      (∀ p, φ p = ∑ k, x k p.1 * y k p.2) ∧
      (∀ k l, k ≠ l → ∑ i, x k i * conj (x l i) = 0) ∧
      (∀ k l, ∑ j, y k j * conj (y l j) = if k = l then 1 else 0) := by
  set Φ : Matrix I J ℂ := Matrix.of fun i j => φ (i, j) with hΦ
  have hH : (Φᴴ * Φ).IsHermitian := (Matrix.posSemidef_conjTranspose_mul_self Φ).isHermitian
  set U : Matrix J J ℂ := (hH.eigenvectorUnitary : Matrix J J ℂ) with hU
  have hD : star U * (Φᴴ * Φ) * U = Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := conj_eig hH
  have huu : U * star U = 1 := Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have huu' : star U * U = 1 := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  set C : Matrix I J ℂ := Φ * U with hC
  have hCC : Cᴴ * C = Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    rw [hC, Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose U, ← hD]
    simp only [Matrix.mul_assoc]
  refine ⟨fun k => WithLp.toLp 2 (fun i => C i k), fun k => WithLp.toLp 2 (fun j => conj (U j k)),
    ?_, ?_, ?_⟩
  · intro p
    have : Φ = C * star U := by rw [hC, Matrix.mul_assoc, huu, Matrix.mul_one]
    have h := congrArg (fun M => M p.1 p.2) this
    simp only [hΦ, Matrix.of_apply, Matrix.mul_apply, Matrix.star_apply] at h
    simpa using h
  · intro k l hkl
    have h := congrArg (fun M => M l k) hCC
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply_ne _ (Ne.symm hkl)] at h
    simpa [mul_comm] using h
  · intro k l
    have h := congrArg (fun M => M k l) huu'
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at h
    simpa using h

theorem ens_exists {α : Type*} [Fintype α] [DecidableEq α] (ρ : Matrix α α ℂ)
    (hρ : IsDensityMatrix ρ) : ∃ e : PureEnsemble α, ensembleDensity e.weight e.vector = ρ := by
  have hH : ρ.IsHermitian := hρ.1.isHermitian
  have hpos := hρ.1.eigenvalues_nonneg
  set U : Matrix α α ℂ := (hH.eigenvectorUnitary : Matrix α α ℂ) with hU
  have hD : star U * ρ * U = Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := conj_eig hH
  have huu : U * star U = 1 := Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have huu' : star U * U = 1 := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hρU : ρ = U * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := by
    rw [← hD]
    simp only [← Matrix.mul_assoc, huu, Matrix.one_mul]
    rw [Matrix.mul_assoc, huu, Matrix.mul_one]
  have htr : ∑ i, hH.eigenvalues i = 1 := by
    have := hH.trace_eq_sum_eigenvalues
    rw [hρ.2] at this
    have := congrArg Complex.re this
    simpa using this.symm
  set σ := (Fintype.equivFin α).symm
  refine ⟨⟨Fintype.card α, fun m => hH.eigenvalues (σ m),
    fun m => WithLp.toLp 2 (fun i => U i (σ m)), fun m => hpos _, ?_, ?_⟩, ?_⟩
  · rw [Equiv.sum_comp σ (fun i => hH.eigenvalues i)]; exact htr
  · intro m
    unfold IsState
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    have h := congrArg (fun M => M (σ m) (σ m)) huu'
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.re_sum, Complex.one_re] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re]
  · simp only [ensembleDensity]
    rw [Equiv.sum_comp σ (fun k => ((hH.eigenvalues k : ℝ) : ℂ) •
      pureDensity (WithLp.toLp 2 (fun i => U i k) : EuclideanSpace ℂ α))]
    conv_rhs => rw [hρU]
    ext i j
    simp [Matrix.mul_apply, Matrix.sum_apply, pureDensity, Matrix.diagonal_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

end X4NN

-- ===== NNU =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace X4NN

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P03

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- squared norm of a vector. -/
def lam {α : Type*} [Fintype α] (x : EuclideanSpace ℂ α) : ℝ := ∑ i, Complex.normSq (x i)

lemma lam_nonneg {α : Type*} [Fintype α] (x : EuclideanSpace ℂ α) : 0 ≤ lam x :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

lemma lam_eq {α : Type*} [Fintype α] (x : EuclideanSpace ℂ α) :
    ((lam x : ℝ) : ℂ) = ∑ i, x i * conj (x i) := by
  rw [lam, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj]

lemma trace_outer {α : Type*} [Fintype α] (x y : EuclideanSpace ℂ α) :
    (outer x y).trace = ∑ i, x i * conj (y i) := rfl

lemma eq_zero_of_lam {α : Type*} [Fintype α] (x : EuclideanSpace ℂ α) (h : lam x = 0) : x = 0 := by
  ext i
  exact Complex.normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => Complex.normSq_nonneg (x j))).1 h i (Finset.mem_univ _))

section
variable (x : J → EuclideanSpace ℂ I) (y : J → EuclideanSpace ℂ J)

lemma pure_eq2 (φ : EuclideanSpace ℂ (I × J)) (hφ : ∀ p, φ p = ∑ k, x k p.1 * y k p.2) :
    pureDensity φ = ∑ k, ∑ l,
      Matrix.kronecker (outer (x k) (x l)) (outer (y k) (y l)) := by
  ext p q
  simp only [pureDensity, Matrix.of_apply, hφ, map_sum, Matrix.sum_apply, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  change _ = (outer (x k) (x l) p.1 q.1 * outer (y k) (y l) p.2 q.2)
  simp [outer]
  ring

variable (hx : ∀ k l, k ≠ l → ∑ i, x k i * conj (x l i) = 0)
  (hy : ∀ k l, ∑ j, y k j * conj (y l j) = if k = l then 1 else 0)
include hx hy

lemma lam_total (φ : EuclideanSpace ℂ (I × J)) (hφ : ∀ p, φ p = ∑ k, x k p.1 * y k p.2)
    (h1 : ‖φ‖ = 1) : ∑ k, lam (x k) = 1 := by
  have h := normSq_one φ h1
  have h2 : ((∑ p, Complex.normSq (φ p) : ℝ) : ℂ) = (pureDensity φ).trace := by
    rw [Complex.ofReal_sum, Matrix.trace]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [pureDensity, Complex.mul_conj]
  rw [h, pure_eq2 x y φ hφ, Matrix.trace_sum] at h2
  simp only [Matrix.trace_sum] at h2
  have tk : ∀ k l, (Matrix.kronecker (outer (x k) (x l)) (outer (y k) (y l))).trace =
      (outer (x k) (x l)).trace * (outer (y k) (y l)).trace :=
    fun k l => Matrix.trace_kronecker (outer (x k) (x l)) (outer (y k) (y l))
  simp only [tk] at h2
  simp only [trace_outer, hy, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2
  have : ((∑ k, lam (x k) : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_sum]; simp only [lam_eq]; exact h2.symm
  exact_mod_cast this

lemma decomp2 {m n r : ℕ} (z : Parameters m n r) (φ : EuclideanSpace ℂ (I × J))
    (hφ : ∀ p, φ p = ∑ k, x k p.1 * y k p.2) (h1 : ‖φ‖ = 1) :
    enhanced z (pureDensity φ) =
      ∑ k, ((lam (x k) : ℝ) : ℂ) • enhanced z (((lam (x k) : ℝ) : ℂ)⁻¹ •
        Matrix.kronecker (outer (x k) (x k)) (outer (y k) (y k))) +
      ∑ k, ∑ l, ((if k = l then 0 else 1 : ℝ) : ℂ) • offd (x k) (x l) (y k) (y l) := by
  have hp : ∑ k, ((lam (x k) : ℝ) : ℂ) = 1 := by exact_mod_cast lam_total x y hx hy φ hφ h1
  have hd : ∀ k, ((lam (x k) : ℝ) : ℂ) • enhanced z (((lam (x k) : ℝ) : ℂ)⁻¹ •
        Matrix.kronecker (outer (x k) (x k)) (outer (y k) (y k))) =
      ((lam (x k) : ℝ) : ℂ) • enhanced z 0 +
        lin z (Matrix.kronecker (outer (x k) (x k)) (outer (y k) (y k))) := by
    intro k
    by_cases h0 : lam (x k) = 0
    · have hx0 := eq_zero_of_lam _ h0
      have : Matrix.kronecker (outer (x k) (x k)) (outer (y k) (y k)) = 0 := by
        ext p q; simp [outer, hx0]
      rw [this, h0]; simp
    · have h0' : ((lam (x k) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0
      rw [enh_eq z, smul_add, map_smul, smul_smul, mul_inv_cancel₀ h0', one_smul]
  rw [enh_eq, pure_eq2 x y φ hφ, map_sum]
  simp only [map_sum]
  rw [Finset.sum_congr rfl fun k _ => hd k]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul, hp, one_smul, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : ∀ l, lin z (Matrix.kronecker (outer (x k) (x l)) (outer (y k) (y l))) =
      (if k = l then lin z (Matrix.kronecker (outer (x k) (x k)) (outer (y k) (y k))) else 0) +
      ((if k = l then 0 else 1 : ℝ) : ℂ) • offd (x k) (x l) (y k) (y l) := by
    intro l
    by_cases h : k = l
    · subst h; simp
    · have hyk : ∑ j, y k j * conj (y l j) = 0 := by rw [hy k l, if_neg h]
      rw [if_neg h, if_neg h, zero_add, lin_off z _ _ _ _ (hx k l h) hyk]
      simp
  rw [Finset.sum_congr rfl fun l _ => e l]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma lam_y (k : J) : lam (y k) = 1 := by
  have h := hy k k
  rw [if_pos rfl, ← lam_eq] at h
  exact_mod_cast h

theorem pure_bound {m n r : ℕ} (z : Parameters m n r) (φ : EuclideanSpace ℂ (I × J))
    (hφ : ∀ p, φ p = ∑ k, x k p.1 * y k p.2) (h1 : ‖φ‖ = 1) :
    nn (enhanced z (pureDensity φ)) ≤ separableBound z +
      ∑ k, ∑ l, (if k = l then 0 else Real.sqrt (lam (x k)) * Real.sqrt (lam (x l))) := by
  rw [decomp2 x y hx hy z φ hφ h1]
  refine (nn_add _ _).trans (add_le_add ?_ ?_)
  · refine (nn_sum _ _ (fun k _ => lam_nonneg _) _).trans ?_
    have hb : ∀ k, lam (x k) * nn (enhanced z (((lam (x k) : ℝ) : ℂ)⁻¹ •
        Matrix.kronecker (outer (x k) (x k)) (outer (y k) (y k)))) ≤ lam (x k) * separableBound z := by
      intro k
      by_cases h0 : lam (x k) = 0
      · rw [h0, zero_mul, zero_mul]
      · refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (lam_nonneg _)
        have h0' : ((lam (x k) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0
        have sk : ((lam (x k) : ℝ) : ℂ)⁻¹ • Matrix.kronecker (outer (x k) (x k)) (outer (y k) (y k))
            = Matrix.kronecker (((lam (x k) : ℝ) : ℂ)⁻¹ • outer (x k) (x k)) (outer (y k) (y k)) :=
          (Matrix.smul_kronecker (((lam (x k) : ℝ) : ℂ)⁻¹) (outer (x k) (x k))
            (outer (y k) (y k))).symm
        rw [sk]
        have tA : (((lam (x k) : ℝ) : ℂ)⁻¹ • outer (x k) (x k)).trace = 1 := by
          rw [Matrix.trace_smul, trace_outer, ← lam_eq, smul_eq_mul, inv_mul_cancel₀ h0']
        have tB : (outer (y k) (y k)).trace = 1 := by
          rw [trace_outer, ← lam_eq, lam_y x y hx hy k]; simp
        rw [enh_prod z _ _ tA tB]
        apply unit_bound
        · have : ∀ p, columnVec (((lam (x k) : ℝ) : ℂ)⁻¹ • outer (x k) (x k)) p =
              ((lam (x k) : ℝ) : ℂ)⁻¹ * columnVec (outer (x k) (x k)) p := fun p => rfl
          simp only [this, Complex.normSq_mul, ← Finset.mul_sum, colvec_normSq]
          change Complex.normSq ((lam (x k) : ℂ))⁻¹ * (lam (x k) * lam (x k)) = 1
          rw [Complex.normSq_inv, Complex.normSq_ofReal]
          field_simp
        · simp only [Complex.normSq_conj, colvec_normSq]
          change lam (y k) * lam (y k) = 1
          rw [lam_y x y hx hy k, one_mul]
    refine (Finset.sum_le_sum fun k _ => hb k).trans_eq ?_
    rw [← Finset.sum_mul, lam_total x y hx hy φ hφ h1, one_mul]
  · have e : ∀ X : J → Matrix (Fin m ⊕ (I × I)) (Fin n ⊕ (J × J)) ℂ,
        ∑ k, X k = ∑ k, ((1 : ℝ) : ℂ) • X k := fun X => by simp
    rw [e]
    refine (nn_sum _ _ (fun _ _ => zero_le_one) _).trans ?_
    simp only [one_mul]
    refine Finset.sum_le_sum fun k _ => (nn_sum _ _ (fun l _ => ?_) _).trans_eq ?_
    · split_ifs <;> norm_num
    · refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs
      · simp
      · rw [one_mul, offd, nn_rank1]
        simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, map_zero,
          Finset.sum_const_zero, zero_add, Pi.star_apply]
        simp only [Complex.star_def, Complex.normSq_conj, colvec_normSq]
        change Real.sqrt (lam (x k) * lam (x l)) * Real.sqrt (lam (y k) * lam (y l)) = _
        rw [lam_y x y hx hy, lam_y x y hx hy, one_mul, Real.sqrt_one, mul_one,
          Real.sqrt_mul (lam_nonneg _)]

end

end X4NN

-- ===== NNV =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace X4NN

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P03

lemma kron_apply {α β : Type*} (A : Matrix α α ℂ) (B : Matrix β β ℂ) (p q : α × β) :
    Matrix.kronecker A B p q = A p.1 q.1 * B p.2 q.2 := rfl

/-- off-diagonal double sum as a sum over `S.offDiag`. -/
lemma offdiag_sum {K : Type*} [Fintype K] [DecidableEq K] (S : Finset K) (f : K → K → ℝ)
    (hf : ∀ k l, (k ∉ S ∨ l ∉ S) → f k l = 0) :
    ∑ k, ∑ l, (if k = l then 0 else f k l) = ∑ p ∈ S.offDiag, f p.1 p.2 := by
  rw [← Fintype.sum_prod_type (f := fun p : K × K => if p.1 = p.2 then 0 else f p.1 p.2)]
  symm
  calc ∑ p ∈ S.offDiag, f p.1 p.2 = ∑ p ∈ S.offDiag, (if p.1 = p.2 then 0 else f p.1 p.2) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [if_neg (Finset.mem_offDiag.1 hp).2.2]
    _ = _ := by
        refine Finset.sum_subset (Finset.subset_univ _) fun p _ hp => ?_
        rw [Finset.mem_offDiag] at hp
        split_ifs with h
        · rfl
        · apply hf
          by_contra hc
          push Not at hc
          exact hp ⟨hc.1, hc.2, h⟩

lemma cs_ineq {K : Type*} [Fintype K] [DecidableEq K] (lm : K → ℝ) (hl : ∀ k, 0 ≤ lm k)
    (ht : ∑ k, lm k = 1) (d : ℕ) (hd : 2 ≤ d)
    (hN : (Finset.univ.filter fun k => lm k ≠ 0).card ≤ d) :
    Real.sqrt 2 / Real.sqrt (((d : ℝ) - 1) * (d : ℝ)) *
      (∑ k, ∑ l, (if k = l then 0 else Real.sqrt (lm k) * Real.sqrt (lm l))) ≤
    Real.sqrt (2 * (1 - ∑ k, lm k ^ 2)) := by
  set S := Finset.univ.filter fun k => lm k ≠ 0 with hS
  have hz : ∀ k, k ∉ S → lm k = 0 := by
    intro k hk; simpa [hS] using hk
  set P := ∑ k, ∑ l, (if k = l then 0 else Real.sqrt (lm k) * Real.sqrt (lm l)) with hP
  set Q := ∑ k, ∑ l, (if k = l then 0 else lm k * lm l) with hQ
  have hQ1 : Q = 1 - ∑ k, lm k ^ 2 := by
    have : (∑ k, lm k) ^ 2 = ∑ k, lm k ^ 2 + Q := by
      rw [sq, Finset.sum_mul_sum, hQ, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have e : ∀ l, lm k * lm l = (if k = l then lm k ^ 2 else 0) + (if k = l then 0 else lm k * lm l) := by
        intro l; by_cases h : k = l
        · subst h; simp [sq]
        · simp [h]
      rw [Finset.sum_congr rfl fun l _ => e l]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [ht] at this; linarith
  have hP' : P = ∑ p ∈ S.offDiag, Real.sqrt (lm p.1) * Real.sqrt (lm p.2) := by
    rw [hP]
    apply offdiag_sum
    intro k l h
    rcases h with h | h <;> simp [hz _ h]
  have hQ' : Q = ∑ p ∈ S.offDiag, lm p.1 * lm p.2 := by
    rw [hQ]
    apply offdiag_sum
    intro k l h
    rcases h with h | h <;> simp [hz _ h]
  have hcs : P ^ 2 ≤ ((S.card : ℝ) * S.card - S.card) * Q := by
    rw [hP', hQ']
    have h := sq_sum_le_card_mul_sum_sq (s := S.offDiag)
      (f := fun p => Real.sqrt (lm p.1) * Real.sqrt (lm p.2))
    rw [Finset.offDiag_card] at h
    have hc : ((S.card * S.card - S.card : ℕ) : ℝ) = (S.card : ℝ) * S.card - S.card := by
      rw [Nat.cast_sub (Nat.le_mul_self _)]; push_cast; ring
    rw [hc] at h
    refine h.trans_eq ?_
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [mul_pow, Real.sq_sqrt (hl _), Real.sq_sqrt (hl _)]
  have hQ0 : 0 ≤ Q := by
    rw [hQ']; exact Finset.sum_nonneg fun p _ => mul_nonneg (hl _) (hl _)
  have hP0 : 0 ≤ P := by
    rw [hP']; exact Finset.sum_nonneg fun p _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hNd : (S.card : ℝ) * S.card - S.card ≤ ((d : ℝ) - 1) * d := by
    have : (S.card : ℝ) ≤ d := by exact_mod_cast hN
    have h0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith [mul_nonneg (sub_nonneg.2 this) (by linarith : (0:ℝ) ≤ d + S.card - 1)]
  have hD : 0 < ((d : ℝ) - 1) * d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  rw [← hQ1]
  have hlhs : 0 ≤ Real.sqrt 2 / Real.sqrt (((d : ℝ) - 1) * d) * P :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hP0
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hD.le]
  rw [div_mul_eq_mul_div, div_le_iff₀ hD]
  nlinarith [mul_le_mul_of_nonneg_right hNd hQ0]

variable {dA dB : ℕ}

lemma support_card (x : Fin dB → EuclideanSpace ℂ (Fin dA))
    (hx : ∀ k l, k ≠ l → ∑ i, x k i * conj (x l i) = 0) :
    (Finset.univ.filter fun k => lam (x k) ≠ 0).card ≤ min dA dB := by
  set S := Finset.univ.filter fun k => lam (x k) ≠ 0
  refine le_min ?_ ?_
  · let v : S → EuclideanSpace ℂ (Fin dA) := fun s => x s.1
    have hz : ∀ s, v s ≠ 0 := by
      intro s h
      have hs := s.2
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      apply hs
      simp [v] at h
      simp [lam, h]
    have ho : Pairwise fun s t => inner ℂ (v s) (v t) = 0 := by
      intro s t hst
      have hne : t.1 ≠ s.1 := fun h => hst (Subtype.ext h.symm)
      have := hx t.1 s.1 hne
      simp only [v, PiLp.inner_apply, RCLike.inner_apply]
      rw [← this]
    have hli := linearIndependent_of_ne_zero_of_inner_eq_zero hz ho
    have := hli.fintype_card_le_finrank
    rw [finrank_euclideanSpace_fin, Fintype.card_coe] at this
    exact this
  · exact (Finset.card_le_univ _).trans (by simp)

theorem pure_conc {m n r : ℕ} (z : Parameters m n r) (hd : 2 ≤ min dA dB)
    (φ : EuclideanSpace ℂ (Fin dA × Fin dB)) (h1 : ‖φ‖ = 1) :
    Real.sqrt 2 / Real.sqrt (((min dA dB : ℝ) - 1) * (min dA dB : ℝ)) *
      (nn (enhanced z (pureDensity φ)) - separableBound z) ≤ pureConcurrence φ := by
  obtain ⟨x, y, hφ, hx, hy⟩ := rep φ
  have hb := pure_bound x y hx hy z φ hφ h1
  have htot := lam_total x y hx hy φ hφ h1
  have hρA : traceRight (pureDensity φ) = ∑ k, outer (x k) (x k) := by
    ext i i'
    rw [pure_eq2 x y φ hφ]
    simp only [traceRight, Matrix.of_apply, Matrix.sum_apply, kron_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    have e : ∀ l, ∑ h, outer (x k) (x l) i i' * outer (y k) (y l) h h =
        if k = l then outer (x k) (x k) i i' else 0 := by
      intro l
      rw [← Finset.mul_sum]
      have := hy k l
      simp only [outer, Matrix.of_apply] at this ⊢
      rw [this]
      split_ifs with h
      · subst h; ring
      · ring
    rw [Finset.sum_congr rfl fun l _ => e l]
    simp
  have htr : ((traceRight (pureDensity φ) * traceRight (pureDensity φ)).trace).re =
      ∑ k, lam (x k) ^ 2 := by
    rw [hρA, Finset.sum_mul_sum, Matrix.trace_sum]
    simp only [Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : ∀ l, ((outer (x k) (x k) * outer (x l) (x l)).trace).re =
        if k = l then lam (x k) ^ 2 else 0 := by
      intro l
      have : (outer (x k) (x k) * outer (x l) (x l)).trace =
          (∑ i, x k i * conj (x l i)) * (∑ j, x l j * conj (x k j)) := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, outer, Matrix.of_apply,
          Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [this]
      split_ifs with h
      · subst h
        rw [← lam_eq, sq]
        push_cast; simp [Complex.ofReal_re]
      · rw [hx k l h, zero_mul, Complex.zero_re]
    rw [Finset.sum_congr rfl fun l _ => e l]
    simp
  have hc : pureConcurrence φ = Real.sqrt (2 * (1 - ∑ k, lam (x k) ^ 2)) := by
    simp only [pureConcurrence]
    rw [htr]
  rw [hc]
  have hcs := cs_ineq (fun k => lam (x k)) (fun k => lam_nonneg _) htot (min dA dB) hd
    (support_card x hx)
  have hcnn : 0 ≤ Real.sqrt 2 / Real.sqrt (((min dA dB : ℝ) - 1) * (min dA dB : ℝ)) :=
    div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  push_cast at hcs
  refine le_trans ?_ hcs
  apply mul_le_mul_of_nonneg_left _ hcnn
  linarith

theorem conc_bound [NeZero dA] [NeZero dB] {m n r : ℕ} (z : Parameters m n r) (hd : 2 ≤ min dA dB)
    (rho : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) (hrho : IsDensityMatrix rho) :
    concurrence rho ≥ Real.sqrt 2 / Real.sqrt (((min dA dB : ℝ) - 1) * (min dA dB : ℝ)) *
      (nuclearNorm (enhanced z rho) - separableBound z) := by
  set c := Real.sqrt 2 / Real.sqrt (((min dA dB : ℝ) - 1) * (min dA dB : ℝ))
  have hc : 0 ≤ c := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  obtain ⟨e0, he0⟩ := ens_exists rho hrho
  unfold concurrence convexRoof
  show _ ≤ _
  refine le_csInf ⟨_, e0, he0, rfl⟩ ?_
  rintro a ⟨e, he, rfl⟩
  rw [← he, nuclear_eq]
  unfold ensembleDensity
  rw [enh_affine z e.weight e.total]
  have h1 := nn_sum Finset.univ e.weight (fun k _ => e.nonnegative k)
    (fun k => enhanced z (pureDensity (e.vector k)))
  have h2 : ∀ k, e.weight k * (c * (nn (enhanced z (pureDensity (e.vector k))) - separableBound z)) ≤
      e.weight k * pureConcurrence (e.vector k) :=
    fun k => mul_le_mul_of_nonneg_left (pure_conc z hd _ (e.normalized k)) (e.nonnegative k)
  have h3 := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => h2 k
  have h4 : ∑ k, e.weight k * (c * (nn (enhanced z (pureDensity (e.vector k))) - separableBound z)) =
      c * (∑ k, e.weight k * nn (enhanced z (pureDensity (e.vector k))) - separableBound z) := by
    have : ∀ k, e.weight k * (c * (nn (enhanced z (pureDensity (e.vector k))) - separableBound z)) =
        c * (e.weight k * nn (enhanced z (pureDensity (e.vector k)))) -
          (c * separableBound z) * e.weight k := fun k => by ring
    rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, e.total]
    ring
  calc c * (nn (∑ k, (e.weight k : ℂ) • enhanced z (pureDensity (e.vector k))) - separableBound z)
      ≤ c * (∑ k, e.weight k * nn (enhanced z (pureDensity (e.vector k))) - separableBound z) :=
        mul_le_mul_of_nonneg_left (by linarith) hc
    _ ≤ _ := h4 ▸ h3

end X4NN

-- ===== NNSol4 =====

noncomputable section

open scoped Matrix ComplexConjugate

section
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P03

theorem solution {dA dB m n r : ℕ} [NeZero dA] [NeZero dB]
    (z : Parameters m n r) (hd : 2 ≤ min dA dB)
    (rho : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hrho : IsDensityMatrix rho) :
    concurrence rho ≥ Real.sqrt 2 / Real.sqrt (((min dA dB : ℝ) - 1) * (min dA dB : ℝ)) *
      (nuclearNorm (enhanced z rho) - separableBound z) :=
  X4NN.conc_bound z hd rho hrho

end

end
