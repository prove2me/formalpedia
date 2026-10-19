-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P08.axialCriterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:06:49.959991+00:00
-- url     : https://prove2.me/submissions/de29038e-8c4b-4813-a5b9-68cbdb7ec529

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P08_Model
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder ComplexConjugate Kronecker
open QAlgorithms QAlgorithms.Entanglement QAlgorithms.QubitChannels
open QAlgorithms.Papers.Independent.Independent1.P08

@[simp] private lemma transpose_apply (X : Matrix Bool Bool ℂ) : transposeMap X = Xᵀ := rfl

private lemma cp_comp (F G : QMap) (hF : IsCompletelyPositive F)
    (hG : IsCompletelyPositive G) : IsCompletelyPositive (F.comp G) := by
  intro r X hX
  exact hF r _ (hG r X hX)

-- Transposing the entire amplified matrix reverses both the reference blocks and entries.
private lemma cp_transpose (F : QMap) (hF : IsCompletelyPositive F) :
    IsCompletelyPositive (transposeMap.comp (F.comp transposeMap)) := by
  intro r X hX
  have h := (hF r Xᵀ hX.transpose).transpose
  have he : idTensorSuperop (transposeMap.comp (F.comp transposeMap)) X =
      (idTensorSuperop F Xᵀ)ᵀ := by ext p q; rfl
  rw [he]
  exact h

private def sandwich (A : Matrix Bool Bool ℂ) : QMap where
  toFun X := A * X * Aᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

private lemma cp_sandwich (A : Matrix Bool Bool ℂ) : IsCompletelyPositive (sandwich A) := by
  intro r X hX
  have h := hX.mul_mul_conjTranspose_same
    ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ A)
  suffices he : idTensorSuperop (sandwich A) X =
      ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ A) * X *
        ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ A)ᴴ by
    rw [he]; exact h
  ext p q
  simp [idTensorSuperop,sandwich,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Fintype.sum_prod_type,Matrix.one_apply,apply_ite,
    eq_comm]

private lemma canonical_entries (t lam : Bloch) (X : Matrix Bool Bool ℂ) :
    canonical t lam X = Matrix.of (fun i k : Bool =>
      if i then
        (if k then (X false false+X true true)/2*(1-(t 2 : ℂ)) -
          (lam 2 : ℂ)*(X false false-X true true)/2
        else (X false false+X true true)/2*((t 0 : ℂ)+Complex.I*(t 1 : ℂ)) +
          ((lam 0 : ℂ)*(X false true+X true false)-(lam 1 : ℂ)*(X false true-X true false))/2)
      else
        (if k then (X false false+X true true)/2*((t 0 : ℂ)-Complex.I*(t 1 : ℂ)) +
          ((lam 0 : ℂ)*(X false true+X true false)+(lam 1 : ℂ)*(X false true-X true false))/2
        else (X false false+X true true)/2*(1+(t 2 : ℂ)) +
          (lam 2 : ℂ)*(X false false-X true true)/2)) := by
  ext i k
  cases i <;> cases k <;>
    simp [canonical,blochAffineMap,sigma,pauliX,pauliY,pauliZ,Matrix.mul_apply,
      Matrix.trace,Fin.sum_univ_succ,Matrix.diagonal_apply] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

private lemma psd_two (a d : ℝ) (b : ℂ) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hdet : Complex.normSq b ≤ a*d) :
    (Matrix.of fun i j : Bool => if i then (if j then (d : ℂ) else star b)
      else (if j then b else (a : ℂ))).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    cases i <;> cases j <;> simp [Matrix.conjTranspose_apply]
  · intro v
    apply Complex.nonneg_iff.mpr
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_bool, Matrix.of_apply,
      Bool.false_eq_true, if_false, if_true, Pi.star_apply]
    constructor
    · simp only [Complex.star_def, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
      have hbd : b.re^2+b.im^2 ≤ a*d := by simpa [Complex.normSq_apply, pow_two] using hdet
      have hv := sq_nonneg (v true |>.re)
      have hw := sq_nonneg (v true |>.im)
      by_cases hz : a = 0
      · subst a
        have hb0 : b.re = 0 := by nlinarith [sq_nonneg b.im,sq_nonneg b.re]
        have hb1 : b.im = 0 := by nlinarith [sq_nonneg b.im,sq_nonneg b.re]
        simp [hb0,hb1]
        nlinarith only [mul_nonneg hd hv,mul_nonneg hd hw]
      · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
        have h1 := sq_nonneg (a*(v false).re+b.re*(v true).re-b.im*(v true).im)
        have h2 := sq_nonneg (a*(v false).im+b.re*(v true).im+b.im*(v true).re)
        have h3 := mul_nonneg (sub_nonneg.mpr hbd) (add_nonneg hv hw)
        apply nonneg_of_mul_nonneg_right (a := a) ?_ hap
        convert add_nonneg (add_nonneg h1 h2) h3 using 1; ring

    · simp [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring

private lemma bloch_entries (t : Bloch) :
    blochDensity t = Matrix.of (fun i j : Bool =>
      if i then (if j then (((1-t 2)/2 : ℝ) : ℂ) else ((t 0 : ℂ)+Complex.I*(t 1 : ℂ))/2)
      else (if j then ((t 0 : ℂ)-Complex.I*(t 1 : ℂ))/2 else (((1+t 2)/2 : ℝ) : ℂ))) := by
  ext i j
  cases i <;> cases j <;>
    simp [blochDensity,sigma,pauliX,pauliY,pauliZ,Fin.sum_univ_succ] <;> ring

private lemma bloch_density (t : Bloch) (h : t 0^2+t 1^2+t 2^2 ≤ 1) :
    IsDensityMatrix (blochDensity t) := by
  have hz : -1 ≤ t 2 ∧ t 2 ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (t 0),sq_nonneg (t 1),sq_nonneg (t 2 + 1),sq_nonneg (t 2 - 1)]
  constructor
  · rw [bloch_entries]
    have hp := psd_two ((1+t 2)/2) ((1-t 2)/2)
      (((t 0 : ℂ)-Complex.I*(t 1 : ℂ))/2) (by linarith) (by linarith) (by
        simp [Complex.normSq_apply]
        nlinarith)
    convert hp using 1
    ext i j
    cases i <;> cases j <;> simp
  · rw [bloch_entries]
    simp [Matrix.trace]
    ring

private lemma bell_entries (i j k l : Bool) :
    pureDensity bell (i,j) (k,l) = if i = j ∧ k = l then (1/2 : ℂ) else 0 := by
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1/2 : ℝ) := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt (by norm_num)]
    norm_num
  cases i <;> cases j <;> cases k <;> cases l <;>
    norm_num [pureDensity,bell,finiteMaxEntangled] <;> simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat] using congrArg Complex.ofReal hr

private lemma choi_complement (t lam : Bloch) :
    (1/2 : ℂ) • (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) - choiState (canonical t lam) =
      choiState (canonical (-t) (-lam)) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  cases i <;> cases j <;> cases k <;> cases l <;>
    norm_num [choiState,idTensorSuperop,canonical_entries,bell_entries,Matrix.one_apply] <;> ring

private lemma choi_positive (Phi : QMap) (h : IsCompletelyPositive Phi) :
    (choiState Phi).PosSemidef := by
  have hb : (pureDensity bell).PosSemidef := by
    exact Matrix.posSemidef_vecMulVec_self_star _
  have hp := h 2
    ((pureDensity bell).submatrix (fun p : Fin 2 × Bool => (finTwoEquiv p.1,p.2))
      (fun p : Fin 2 × Bool => (finTwoEquiv p.1,p.2)))
    (hb.submatrix (fun p : Fin 2 × Bool => (finTwoEquiv p.1,p.2)))
  have hf := hp.submatrix (fun p : Bool × Bool => (finTwoEquiv.symm p.1,p.2))
  convert hf using 1
  ext p q
  simp [choiState,idTensorSuperop]

private lemma canonical_tp (t lam : Bloch) : TracePreserving (canonical t lam) := by
  intro X
  simp [Matrix.trace,canonical_entries]
  ring

private lemma amp_smul (F : QMap) {r : ℕ} (c : ℂ)
    (X : Matrix (Fin r × Bool) (Fin r × Bool) ℂ) :
    idTensorSuperop F (c • X) = c • idTensorSuperop F X := by
  ext p q
  change F (c • Matrix.of (fun i j => X (p.1,i) (q.1,j))) p.2 q.2 =
    c * F (Matrix.of (fun i j => X (p.1,i) (q.1,j))) p.2 q.2
  rw [map_smul]
  rfl

private lemma density_test_cp (F : QMap)
    (h : ∀ r : ℕ, 0 < r → ∀ X : Matrix (Fin r × Bool) (Fin r × Bool) ℂ,
      IsDensityMatrix X → (idTensorSuperop F X).PosSemidef) :
    IsCompletelyPositive F := by
  intro r X hX
  by_cases hr : r = 0
  · subst r
    have he : idTensorSuperop F X = 0 := Subsingleton.elim _ _
    rw [he]
    exact Matrix.PosSemidef.zero
  have ht := Complex.nonneg_iff.mp hX.trace_nonneg
  have htrace : X.trace = (X.trace.re : ℂ) := by
    apply Complex.ext <;> simp [ht.2.symm]
  by_cases hz : X.trace.re = 0
  · have hx0 : X = 0 := hX.trace_eq_zero_iff.mp (by rw [htrace,hz]; simp)
    subst X
    have he : idTensorSuperop F (0 : Matrix (Fin r × Bool) (Fin r × Bool) ℂ) = 0 := by
      ext p q
      change F 0 p.2 q.2 = 0
      simp
    rw [he]
    exact Matrix.PosSemidef.zero
  let Y := (X.trace.re⁻¹ : ℂ) • X
  have hY : IsDensityMatrix Y := by
    refine ⟨hX.smul (by exact_mod_cast inv_nonneg.mpr ht.1), ?_⟩
    change ((↑X.trace.re : ℂ)⁻¹ • X).trace = 1
    rw [Matrix.trace_smul]
    calc
      (↑X.trace.re : ℂ)⁻¹ * X.trace = (↑X.trace.re : ℂ)⁻¹ * ↑X.trace.re :=
        congrArg (fun z : ℂ => (↑X.trace.re : ℂ)⁻¹ * z) htrace
      _ = 1 := inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hz)
  have hp := (h r (Nat.pos_of_ne_zero hr) Y hY).smul
    (by exact_mod_cast ht.1 : (0 : ℂ) ≤ X.trace.re)
  have he : (X.trace.re : ℂ) • idTensorSuperop F Y = idTensorSuperop F X := by
    rw [show Y = (↑X.trace.re : ℂ)⁻¹ • X from rfl, amp_smul, smul_smul,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hz), one_smul]
  rw [he] at hp
  exact hp

private lemma eb_cp_and_transpose (F : QMap) (h : IsEntanglementBreaking F) :
    IsCompletelyPositive F ∧ IsCompletelyPositive (transposeMap.comp F) := by
  constructor <;> apply density_test_cp <;> intro r hr X hX <;>
    have : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  · obtain ⟨q,w,A,B,hw,_,hAB,he⟩ := h r hr X hX
    rw [he]
    exact Matrix.posSemidef_sum _ fun j _ =>
      ((hAB j).1.1.kronecker (hAB j).2.1).smul
        (by exact_mod_cast hw j : (0 : ℂ) ≤ w j)
  · obtain ⟨q,w,A,B,hw,_,hAB,he⟩ := h r hr X hX
    have he' : idTensorSuperop (transposeMap.comp F) X =
        ∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)ᵀ := by
      ext p u
      have hh := congrFun (congrFun he (p.1,u.2)) (u.1,p.2)
      simpa [idTensorSuperop,Matrix.sum_apply] using hh
    rw [he']
    exact Matrix.posSemidef_sum _ fun j _ =>
      ((hAB j).1.1.kronecker (hAB j).2.1.transpose).smul
        (by exact_mod_cast hw j : (0 : ℂ) ≤ w j)


private def twoR (a d b : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.of fun i j => if i then (if j then (d : ℂ) else (b : ℂ))
    else (if j then (b : ℂ) else (a : ℂ))

private lemma twoR_psd (a d b : ℝ) :
    (twoR a d b).PosSemidef ↔ 0 ≤ a ∧ 0 ≤ d ∧ b^2 ≤ a*d := by
  constructor
  · intro h
    have ha := Complex.nonneg_iff.mp (h.diag_nonneg (i := false))
    have hd := Complex.nonneg_iff.mp (h.diag_nonneg (i := true))
    have ht := (Complex.nonneg_iff.mp (h.submatrix finTwoEquiv).det_nonneg).1
    simp [twoR, Matrix.det_fin_two, Matrix.submatrix_apply, finTwoEquiv,
      Complex.mul_re] at ha hd ht
    exact ⟨ha,hd,by nlinarith [ht]⟩
  · rintro ⟨ha,hd,hb⟩
    convert psd_two a d (b : ℂ) ha hd (by simpa [Complex.normSq_apply,pow_two] using hb) using 1
    ext i j
    cases i <;> cases j <;> simp [twoR]

private def embed (flip : Bool) : Matrix (Bool × Bool) Bool ℂ :=
  fun p i => if p = (i, xor i flip) then 1 else 0

private def xmat (t x y z : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  embed false * twoR (1+z+t) (1+z-t) (x+y) * (embed false)ᴴ +
  embed true * twoR (1-z-t) (1-z+t) (x-y) * (embed true)ᴴ

private lemma xmat_blocks (t x y z : ℝ) :
    (xmat t x y z).PosSemidef ↔
      (twoR (1+z+t) (1+z-t) (x+y)).PosSemidef ∧
      (twoR (1-z-t) (1-z+t) (x-y)).PosSemidef := by
  constructor
  · intro h
    constructor
    · convert h.submatrix (fun i : Bool => (i,i)) using 1
      ext i j
      cases i <;> cases j <;>
        simp [xmat,embed,twoR,Matrix.mul_apply,Matrix.conjTranspose_apply]
    · convert h.submatrix (fun i : Bool => (i,!i)) using 1
      ext i j
      cases i <;> cases j <;>
        simp [xmat,embed,twoR,Matrix.mul_apply,Matrix.conjTranspose_apply]
  · rintro ⟨hA,hB⟩
    exact (hA.mul_mul_conjTranspose_same (embed false)).add
      (hB.mul_mul_conjTranspose_same (embed true))

private lemma axial_choi (t : ℝ) (lam : Bloch) :
    choiState (canonical ![0,0,t] lam) =
      (1/4 : ℂ) • xmat t (lam 0) (lam 1) (lam 2) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  cases i <;> cases j <;> cases k <;> cases l <;>
    norm_num [choiState,idTensorSuperop,canonical_entries,bell_entries,xmat,embed,twoR,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.cons_val_two] <;> ring

private lemma xmat_psd (t x y z : ℝ) :
    (xmat t x y z).PosSemidef ↔
      (0 ≤ 1+z+t ∧ 0 ≤ 1+z-t ∧ 0 ≤ 1-z-t ∧ 0 ≤ 1-z+t) ∧
      (x+y)^2 ≤ (1+z)^2-t^2 ∧ (x-y)^2 ≤ (1-z)^2-t^2 := by
  rw [xmat_blocks,twoR_psd,twoR_psd]
  constructor
  · rintro ⟨⟨ha,hb,hc⟩,⟨hd,he,hf⟩⟩
    exact ⟨⟨ha,hb,hd,he⟩,by nlinarith,by nlinarith⟩
  · rintro ⟨⟨ha,hb,hd,he⟩,hc,hf⟩
    exact ⟨⟨ha,hb,by nlinarith⟩,⟨hd,he,by nlinarith⟩⟩

private lemma scale_psd (A : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    ((1/4 : ℂ) • A).PosSemidef ↔ A.PosSemidef := by
  constructor
  · intro h
    have hh := h.smul (by norm_num : (0 : ℂ) ≤ 4)
    simpa [smul_smul] using hh
  · exact fun h => h.smul (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 1/4)

private lemma diag_strip (t z : ℝ) :
    (0 ≤ 1+z+t ∧ 0 ≤ 1+z-t ∧ 0 ≤ 1-z-t ∧ 0 ≤ 1-z+t) ↔ |z|+|t| ≤ 1 := by
  rcases le_total 0 z with hz | hz <;> rcases le_total 0 t with ht | ht <;>
    simp only [abs_of_nonneg, abs_of_nonpos, hz, ht] <;> constructor
  all_goals
    intro h
    repeat' apply And.intro
    all_goals linarith

private lemma square_pair (x y q : ℝ) :
    ((x+y)^2 ≤ q ∧ (x-y)^2 ≤ q) ↔ (|x|+|y|)^2 ≤ q := by
  have hprod := mul_nonneg (abs_nonneg x) (abs_nonneg y)
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy <;>
    simp only [abs_of_nonneg, abs_of_nonpos, hx, hy] at hprod ⊢ <;> constructor
  all_goals
    intro h
    repeat' apply And.intro
    all_goals nlinarith

private lemma square_bounds (z t q : ℝ) :
    (q ≤ (1+z)^2-t^2 ∧ q ≤ (1-z)^2-t^2) ↔ q ≤ (1-|z|)^2-t^2 := by
  rcases le_total 0 z with hz | hz <;>
    simp only [abs_of_nonneg, abs_of_nonpos, hz] <;> constructor
  all_goals
    intro h
    repeat' apply And.intro
    all_goals nlinarith

private lemma joint_numeric (t x y z : ℝ) :
    ((xmat t x y z).PosSemidef ∧ (xmat (-t) (-x) (-y) (-z)).PosSemidef) ↔
      |z|+|t| ≤ 1 ∧ (|x|+|y|)^2 ≤ (1-|z|)^2-t^2 := by
  rw [xmat_psd, xmat_psd, diag_strip, diag_strip]
  simp only [abs_neg]
  constructor
  · rintro ⟨⟨hd, h1, h2⟩, ⟨_, h3, h4⟩⟩
    refine ⟨hd, (square_bounds z t ((|x|+|y|)^2)).mp ?_⟩
    constructor
    · exact (square_pair x y _).mp ⟨h1, by nlinarith only [h4]⟩
    · exact (square_pair x y _).mp ⟨by nlinarith only [h3], h2⟩
  · rintro ⟨hd, h⟩
    obtain ⟨hP, hM⟩ := (square_bounds z t ((|x|+|y|)^2)).mpr h
    obtain ⟨hPP, hMP⟩ := (square_pair x y _).mpr hP
    obtain ⟨hPM, hMM⟩ := (square_pair x y _).mpr hM
    exact ⟨⟨hd, hPP, hMM⟩, ⟨hd, by nlinarith only [hPM], by nlinarith only [hMP]⟩⟩

private lemma choi_joint (t : ℝ) (lam : Bloch) :
    ((choiState (canonical ![0,0,t] lam)).PosSemidef ∧
      ((1/2 : ℂ) • (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) -
        choiState (canonical ![0,0,t] lam)).PosSemidef) ↔
      |lam 2|+|t| ≤ 1 ∧ (|lam 0|+|lam 1|)^2 ≤ (1-|lam 2|)^2-t^2 := by
  rw [choi_complement]
  have he : -(![0,0,t] : Bloch) = ![0,0,-t] := by ext i; fin_cases i <;> simp
  rw [he,axial_choi,axial_choi,scale_psd,scale_psd]
  exact joint_numeric t (lam 0) (lam 1) (lam 2)

private def conditional {a : ℕ}
    (F : Matrix Bool Bool ℂ) (X : Matrix (Fin a × Bool) (Fin a × Bool) ℂ) :
    Matrix (Fin a) (Fin a) ℂ :=
  Matrix.of fun i j => (F * X.submatrix (fun t => (i,t)) (fun t => (j,t))).trace

private lemma block_sandwich {a : ℕ} (T : Matrix Bool Bool ℂ)
    (X : Matrix (Fin a × Bool) (Fin a × Bool) ℂ) (i j : Fin a) :
    ((Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) T) * X *
      (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) T)ᴴ).submatrix
        (fun t => (i,t)) (fun t => (j,t)) =
      T * X.submatrix (fun t => (i,t)) (fun t => (j,t)) * Tᴴ := by
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker']
  ext u v
  simp [Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.submatrix_apply]

private lemma traceRight_psd {a : ℕ}
    (X : Matrix (Fin a × Bool) (Fin a × Bool) ℂ) (hX : X.PosSemidef) :
    (traceRight X).PosSemidef := by
  have heq : traceRight X = ∑ t, X.submatrix (fun i => (i,t)) (fun i => (i,t)) := by
    ext i j
    simp [traceRight, Matrix.sum_apply, Matrix.submatrix]
  rw [heq]
  exact Matrix.posSemidef_sum _ fun t _ => hX.submatrix _

private lemma conditional_psd {a : ℕ}
    (F : Matrix Bool Bool ℂ) (hF : F.PosSemidef)
    (X : Matrix (Fin a × Bool) (Fin a × Bool) ℂ) (hX : X.PosSemidef) :
    (conditional F X).PosSemidef := by
  let T := CFC.sqrt F
  have hT : T.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg F)).isHermitian
  have hTT : T * T = F := by simpa [T, pow_two] using CFC.sq_sqrt F hF.nonneg
  let B := Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) T
  have heq : conditional F X = traceRight (B * X * Bᴴ) := by
    ext i j
    change (F * X.submatrix (fun t => (i,t)) (fun t => (j,t))).trace =
      ((B * X * Bᴴ).submatrix (fun t => (i,t)) (fun t => (j,t))).trace
    rw [block_sandwich, hT.eq, Matrix.trace_mul_cycle, hTT]
  rw [heq]
  exact traceRight_psd _ (hX.mul_mul_conjTranspose_same B)

private lemma output_sum {a m : ℕ}
    (R F : Fin m → Matrix Bool Bool ℂ)
    (X : Matrix (Fin a × Bool) (Fin a × Bool) ℂ) :
    idTensorSuperop (Entanglement.holevoMap R F) X =
      ∑ k, Matrix.kronecker (conditional (F k) X) (R k) := by
  ext p q
  simp [idTensorSuperop, Entanglement.holevoMap, conditional,
    Matrix.sum_apply, Matrix.submatrix]

private lemma psd_normalization {a : ℕ} (ha : 0 < a)
    (A : Matrix (Fin a) (Fin a) ℂ) (hA : A.PosSemidef) :
    ∃ B : Matrix (Fin a) (Fin a) ℂ, IsDensityMatrix B ∧ (A.trace.re : ℂ) • B = A := by
  have hr : (A.trace.re : ℂ) = A.trace := Complex.ext rfl hA.trace_nonneg.2
  by_cases hz : A.trace.re = 0
  · have hzero : A = 0 := hA.trace_eq_zero_iff.mp (by rw [← hr, hz]; rfl)
    let B : Matrix (Fin a) (Fin a) ℂ := ((a : ℝ)⁻¹ : ℂ) • 1
    refine ⟨B, ⟨?_, ?_⟩, ?_⟩
    · exact Matrix.PosSemidef.one.smul (by exact_mod_cast inv_nonneg.mpr (Nat.cast_nonneg a))
    · simp [B, Matrix.trace_smul, Matrix.trace_one, ne_of_gt ha]
    · simp [hzero]
  · refine ⟨((A.trace.re)⁻¹ : ℂ) • A, ⟨?_, ?_⟩, ?_⟩
    · exact hA.smul (by exact_mod_cast inv_nonneg.mpr hA.trace_nonneg.1)
    · rw [Matrix.trace_smul, smul_eq_mul, ← hr]
      simpa only [Complex.ofReal_re, Complex.ofReal_inv] using
        inv_mul_cancel₀ (show (A.trace.re : ℂ) ≠ 0 by exact_mod_cast hz)
    · simp only [smul_smul,
        mul_inv_cancel₀ (show (A.trace.re : ℂ) ≠ 0 by exact_mod_cast hz), one_smul]

private lemma output_decomposition {a m : ℕ} (ha : 0 < a)
    (R F : Fin m → Matrix Bool Bool ℂ)
    (hR : ∀ k, IsDensityMatrix (R k)) (hF : ∀ k, (F k).PosSemidef)
    (X : Matrix (Fin a × Bool) (Fin a × Bool) ℂ) (hX : X.PosSemidef) :
    ∃ w : Fin m → ℝ, ∃ B : Fin m → Matrix (Fin a) (Fin a) ℂ,
      (∀ k, 0 ≤ w k) ∧ (∀ k, IsDensityMatrix (B k) ∧ IsDensityMatrix (R k)) ∧
      idTensorSuperop (Entanglement.holevoMap R F) X =
        ∑ k, (w k : ℂ) • Matrix.kronecker (B k) (R k) := by
  have hp k := conditional_psd (F k) (hF k) X hX
  choose B hB hEq using fun k => psd_normalization ha (conditional (F k) X) (hp k)
  refine ⟨fun k => (conditional (F k) X).trace.re, B,
    (fun k => (hp k).trace_nonneg.1), (fun k => ⟨hB k, hR k⟩), ?_⟩
  rw [output_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← hEq k]
  simp only [Matrix.kronecker, Matrix.smul_kronecker]

private lemma output_trace {a m : ℕ}
    (R F : Fin m → Matrix Bool Bool ℂ)
    (hR : ∀ k, IsDensityMatrix (R k)) (hPOVM : IsPOVM F)
    (X : Matrix (Fin a × Bool) (Fin a × Bool) ℂ) :
    (idTensorSuperop (Entanglement.holevoMap R F) X).trace = X.trace := by
  rw [output_sum, Matrix.trace_sum]
  simp only [Matrix.kronecker, Matrix.trace_kronecker]
  simp_rw [(hR _).2, mul_one]
  change (∑ k, ∑ i, (F k * X.submatrix (fun t => (i,t)) (fun t => (i,t))).trace) = _
  rw [Finset.sum_comm]
  have hi (i : Fin a) : (∑ k, (F k * X.submatrix (fun t => (i,t)) (fun t => (i,t))).trace) =
      (X.submatrix (fun t => (i,t)) (fun t => (i,t))).trace := by
    rw [← Matrix.trace_sum, ← Finset.sum_mul, hPOVM.2, Matrix.one_mul]
  simp_rw [hi]
  simp [Matrix.trace, Fintype.sum_prod_type, Matrix.submatrix_apply]

private lemma separable_density_of_trace_one {a : ℕ} [Nonempty (Fin a)] [Nonempty Bool]
    (X : Matrix (Fin a × Bool) (Fin a × Bool) ℂ)
    (hs : Entanglement.IsSeparablePositive X) (ht : X.trace = 1) :
    Entanglement.IsSeparableDensity X := by
  rcases hs with ⟨q, w, A, B, hw, hAB, heq⟩
  refine ⟨q, w, A, B, hw, ?_, hAB, heq⟩
  have h := congrArg Matrix.trace heq
  simp only [Matrix.trace_sum, Matrix.trace_smul, Matrix.kronecker,
    Matrix.trace_kronecker, (hAB _).1.2, (hAB _).2.2, mul_one, smul_eq_mul] at h
  rw [ht] at h
  exact_mod_cast h.symm


private lemma holevo_eb {m : ℕ} (R F : Fin m → Matrix Bool Bool ℂ)
    (hR : ∀ k, IsDensityMatrix (R k)) (hF : IsPOVM F) :
    EBT (holevoMap R F) := by
  constructor
  · intro X
    simp only [holevoMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.trace_sum,
      Matrix.trace_smul, (hR _).2, smul_eq_mul, mul_one]
    rw [← Matrix.trace_sum, ← Finset.sum_mul, hF.2, Matrix.one_mul]
  · intro a ha
    let : Nonempty (Fin a) := ⟨⟨0,ha⟩⟩
    intro X hX
    rcases output_decomposition ha R F hR hF.1 X hX.1 with ⟨w,B,hw,hB,he⟩
    exact separable_density_of_trace_one _ ⟨m,w,B,R,hw,hB,he⟩
      ((output_trace R F hR hF X).trans hX.2)

private def axis (j : Fin 3) (b : Bool) : Matrix Bool Bool ℂ :=
  (2⁻¹ : ℂ) • (1 + (if b then (-1 : ℂ) else 1) • sigma j)

private lemma axis_density (j : Fin 3) (b : Bool) : IsDensityMatrix (axis j b) := by
  have h : axis j b=blochDensity (Pi.single j (if b then -1 else 1)) := by
    simp [axis,blochDensity]
  rw [h]
  apply bloch_density
  fin_cases j <;> cases b <;> norm_num [Pi.single_apply,Fin.ext_iff]

private def pairPOVM (j : Fin 3) : Fin 2 → Matrix Bool Bool ℂ :=
  ![axis j false,axis j true]

private lemma pair_povm (j : Fin 3) : IsPOVM (pairPOVM j) := by
  constructor
  · intro k
    fin_cases k
    · exact (axis_density j false).1
    · exact (axis_density j true).1
  · ext i k
    norm_num [pairPOVM,axis,Fin.sum_univ_succ]
    ring

private def pairEffect (j : Fin 3) (v : ℝ) (b : Bool) : Matrix Bool Bool ℂ :=
  (((|v|+v)/2 : ℝ) : ℂ) • axis j b + (((|v|-v)/2 : ℝ) : ℂ) • axis j (!b)

private lemma pairEffect_psd (j : Fin 3) (v : ℝ) (b : Bool) : (pairEffect j v b).PosSemidef := by
  apply Matrix.PosSemidef.add
  · apply (axis_density j b).1.smul
    exact_mod_cast (show 0 ≤ (|v|+v)/2 by linarith [neg_abs_le v])
  · apply (axis_density j (!b)).1.smul
    exact_mod_cast (show 0 ≤ (|v|-v)/2 by linarith [le_abs_self v])


private lemma eb_complement (t lam : Bloch) (h : EBT (canonical t lam)) :
    ((1/2 : ℂ) • (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) -
      choiState (canonical t lam)).PosSemidef := by
  have hc := cp_comp (sandwich pauliY) (transposeMap.comp (canonical t lam))
    (cp_sandwich _) (eb_cp_and_transpose _ h.2).2
  have he : canonical (-t) (-lam) =
      (sandwich pauliY).comp (transposeMap.comp (canonical t lam)) := by
    ext X i k
    cases i <;> cases k <;>
      simp [canonical_entries,sandwich,pauliY,Matrix.mul_apply,Matrix.conjTranspose_apply] <;>
      ring_nf <;> simp [Complex.I_sq] <;> ring
  rw [← he] at hc
  rw [choi_complement]
  exact choi_positive _ hc

private def axialOutputs (t r b : ℝ) : Fin 6 → Matrix Bool Bool ℂ :=
  ![blochDensity ![r/b,0,t/b], blochDensity ![-(r/b),0,t/b],
    blochDensity ![0,r/b,t/b], blochDensity ![0,-(r/b),t/b],
    blochDensity ![0,0,1], blochDensity ![0,0,-1]]

private def axialEffects (x y z b : ℝ) : Fin 6 → Matrix Bool Bool ℂ :=
  ![((b/(|x|+|y|) : ℝ) : ℂ) • pairEffect 0 x false,
    ((b/(|x|+|y|) : ℝ) : ℂ) • pairEffect 0 x true,
    ((b/(|x|+|y|) : ℝ) : ℂ) • pairEffect 1 y false,
    ((b/(|x|+|y|) : ℝ) : ℂ) • pairEffect 1 y true,
    pairEffect 2 z false, pairEffect 2 z true]

private lemma axial_outputs_density (t r b : ℝ) (hb : 0 < b)
    (h : r^2+t^2 ≤ b^2) : ∀ k, IsDensityMatrix (axialOutputs t r b k) := by
  have hh : (r/b)^2+(t/b)^2 ≤ 1 := by
    rw [div_pow,div_pow,← add_div]
    exact (div_le_one (sq_pos_of_pos hb)).mpr h
  intro k
  fin_cases k <;> apply bloch_density <;>
    norm_num [axialOutputs,Matrix.cons_val_two] <;> nlinarith

private lemma axial_effects_povm (x y z b : ℝ) (hb : 0 ≤ b)
    (hbr : b+|z|=1) (hr : 0 < |x|+|y|) : IsPOVM (axialEffects x y z b) := by
  constructor
  · intro k
    fin_cases k
    all_goals first
      | exact (pairEffect_psd _ _ _).smul
          (by exact_mod_cast div_nonneg hb (le_of_lt hr) : (0 : ℂ) ≤ (b/(|x|+|y|) : ℝ))
      | exact pairEffect_psd _ _ _
  · have hc : (((|x| : ℝ) : ℂ)+((|y| : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt hr
    have he : (1 : Matrix Bool Bool ℂ) = ((b+|z| : ℝ) : ℂ) • 1 := by rw [hbr]; simp
    rw [he]
    ext i j
    cases i <;> cases j <;>
      norm_num [axialEffects,pairEffect,axis,sigma,pauliX,pauliY,pauliZ,Fin.sum_univ_succ] <;>
      field_simp [hc] <;> ring

set_option maxHeartbeats 800000 in
private lemma axial_holevo (t x y z b : ℝ) (hb : b ≠ 0)
    (hr : |x|+|y| ≠ 0) (hbr : b+|z|=1) :
    canonical ![0,0,t] ![x,y,z] =
      holevoMap (axialOutputs t (|x|+|y|) b) (axialEffects x y z b) := by
  have hbc : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  have hrc : (((|x| : ℝ) : ℂ)+((|y| : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hr
  have hzc : ((|z| : ℝ) : ℂ) = 1-(b : ℂ) := by exact_mod_cast (show |z|=1-b by linarith)
  ext X i j
  cases i <;> cases j <;>
    norm_num [canonical_entries,axialOutputs,axialEffects,holevoMap,blochDensity,pairEffect,
      axis,sigma,pauliX,pauliY,pauliZ,Fin.sum_univ_succ,Matrix.cons_val_two,
      Matrix.mul_apply,Matrix.trace] <;>
    (try rw [hzc]) <;> field_simp [hbc,hrc] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

private lemma line_eb (t z : ℝ) (h : |z|+|t| ≤ 1) :
    EBT (canonical ![0,0,t] ![0,0,z]) := by
  let R : Fin 2 → Matrix Bool Bool ℂ :=
    ![blochDensity ![0,0,t+z], blochDensity ![0,0,t-z]]
  have hp : |t+z| ≤ 1 := (abs_add_le t z).trans (by linarith)
  have hm : |t-z| ≤ 1 := (abs_sub t z).trans (by linarith)
  have hR : ∀ k, IsDensityMatrix (R k) := by
    intro k
    fin_cases k <;> apply bloch_density
    · have hh := (sq_le_sq₀ (abs_nonneg (t+z)) (show (0 : ℝ) ≤ 1 by norm_num)).mpr hp
      norm_num [R,Matrix.cons_val_two]
      nlinarith [sq_abs (t+z)]
    · have hh := (sq_le_sq₀ (abs_nonneg (t-z)) (show (0 : ℝ) ≤ 1 by norm_num)).mpr hm
      norm_num [R,Matrix.cons_val_two]
      nlinarith [sq_abs (t-z)]
  have he : canonical ![0,0,t] ![0,0,z] = holevoMap R (pairPOVM 2) := by
    ext X i j
    cases i <;> cases j <;>
      norm_num [canonical_entries,R,pairPOVM,axis,blochDensity,sigma,pauliX,pauliY,pauliZ,
        holevoMap,Matrix.mul_apply,Matrix.trace,Fin.sum_univ_succ,Matrix.cons_val_two] <;> ring
  rw [he]
  exact holevo_eb R (pairPOVM 2) hR (pair_povm 2)

private lemma axial_sufficient (t x y z : ℝ) (hs : |z|+|t| ≤ 1)
    (h : (|x|+|y|)^2 ≤ (1-|z|)^2-t^2) : EBT (canonical ![0,0,t] ![x,y,z]) := by
  by_cases hr : |x|+|y|=0
  · have hx : x=0 := abs_eq_zero.mp (by linarith [abs_nonneg y,abs_nonneg x])
    have hy : y=0 := abs_eq_zero.mp (by linarith [abs_nonneg y,abs_nonneg x])
    subst x; subst y
    exact line_eb t z hs
  · have hrp : 0 < |x|+|y| := lt_of_le_of_ne (add_nonneg (abs_nonneg x) (abs_nonneg y)) (Ne.symm hr)
    have hb : 0 < 1-|z| := by
      have hb0 : 0 ≤ 1-|z| := by linarith [abs_nonneg t]
      nlinarith [sq_pos_of_pos hrp,sq_nonneg t]
    rw [axial_holevo t x y z (1-|z|) (ne_of_gt hb) hr (by ring)]
    exact holevo_eb _ _ (axial_outputs_density _ _ _ hb (by nlinarith))
      (axial_effects_povm _ _ _ _ (le_of_lt hb) (by ring) hrp)

private lemma axial_eb (t : ℝ) (lam : Bloch) :
    EBT (canonical ![0,0,t] lam) ↔
      |lam 2|+|t| ≤ 1 ∧ (|lam 0|+|lam 1|)^2 ≤ (1-|lam 2|)^2-t^2 := by
  constructor
  · intro h
    exact (choi_joint t lam).mp
      ⟨choi_positive _ (eb_cp_and_transpose _ h.2).1,eb_complement _ _ h⟩
  · rintro ⟨hs,h⟩
    have he : lam = ![lam 0,lam 1,lam 2] := by ext i; fin_cases i <;> rfl
    simpa only [← he] using axial_sufficient t (lam 0) (lam 1) (lam 2) hs h

theorem solution :
    (∀ t3 : ℝ, ∀ lam : Bloch, CPT (canonical ![0,0,t3] lam) →
      (EBT (canonical ![0,0,t3] lam) ↔
        (|lam 0|+|lam 1|)^2 ≤ (1-|lam 2|)^2-t3^2)) ∧
    (∀ t3 l3 : ℝ, |l3| ≤ 1 → 0 ≤ (1-|l3|)^2-t3^2 →
      {v : Fin 2 → ℝ | EBT (canonical ![0,0,t3] ![v 0,v 1,l3])} =
        {v | |v 0|+|v 1| ≤ Real.sqrt ((1-|l3|)^2-t3^2)}) := by
  constructor
  · intro t lam hPhi
    rw [axial_eb]
    have hdiag := ((xmat_psd t (lam 0) (lam 1) (lam 2)).mp
      ((scale_psd _).mp (by rw [← axial_choi]; exact choi_positive _ hPhi.2))).1
    have hb : |lam 2|+|t| ≤ 1 := by
      rcases le_total 0 (lam 2) with hz | hz <;> rcases le_total 0 t with ht | ht <;>
        simp [abs_of_nonneg,abs_of_nonpos,hz,ht] <;> linarith [hdiag.1,hdiag.2.1,hdiag.2.2.1,hdiag.2.2.2]
    exact and_iff_right hb
  · intro t z hz hq
    ext v
    change EBT (canonical ![0,0,t] ![v 0,v 1,z]) ↔ _
    rw [axial_eb]
    change (|z|+|t| ≤ 1 ∧ (|v 0|+|v 1|)^2 ≤ (1-|z|)^2-t^2) ↔
      |v 0|+|v 1| ≤ Real.sqrt ((1-|z|)^2-t^2)
    have ht : |z|+|t| ≤ 1 := by
      have h0 := abs_nonneg t
      have h1 := abs_nonneg z
      have hs := sq_abs t
      nlinarith
    rw [and_iff_right ht]
    exact (Real.le_sqrt (by positivity) hq).symm

#print axioms solution
