-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P08.linearChannels
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:49:45.051568+00:00
-- url     : https://prove2.me/submissions/ae41f862-0184-4568-ac63-6877ac650f23

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P08_Model
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

noncomputable section
open scoped Matrix ComplexOrder
open QAlgorithms QAlgorithms.Entanglement QAlgorithms.QubitChannels
open QAlgorithms.Papers.Independent.Independent1.P08

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
        convert add_nonneg (add_nonneg h1 h2) h3 using 1 <;> ring

    · simp [Complex.star_def, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.conj_re,
        Complex.conj_im]
      <;> ring

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
        simp [Complex.normSq_apply,Complex.div_re,Complex.div_im]
        nlinarith)
    convert hp using 1
    ext i j
    cases i <;> cases j <;> simp [Complex.star_def,map_div₀,map_sub,map_mul] <;> ring
  · rw [bloch_entries]
    simp [Matrix.trace,Fintype.sum_bool]
    push_cast
    ring

private lemma bloch_bound (t : Bloch) (h : (blochDensity t).PosSemidef) :
    t 0^2+t 1^2+t 2^2 ≤ 1 := by
  have hd := (h.submatrix finTwoEquiv).det_nonneg
  rw [Matrix.det_fin_two] at hd
  apply Complex.nonneg_iff.mp at hd
  have hr := hd.1
  norm_num [Matrix.submatrix_apply,finTwoEquiv,bloch_entries,Complex.mul_re,
    Complex.mul_im,Complex.div_re,Complex.div_im] at hr
  nlinarith

private lemma linear_formula (t : Bloch) (a : ℝ) :
    canonical t ![0,0,a] = holevoMap
      (fun b : Bool => blochDensity (t + Pi.single 2 (if b then -a else a)))
      (fun b : Bool => pureDensity (ket b)) := by
  ext X i j
  cases i <;> cases j <;>
    simp [canonical,blochAffineMap,holevoMap,blochDensity,sigma,pauliX,pauliY,pauliZ,
      pureDensity,ket,Matrix.mul_apply,Matrix.trace,Fintype.sum_bool,Fin.sum_univ_succ,
      Matrix.diagonal_apply,Pi.single_apply] <;> ring

private lemma output_on_ket (R : Bool → Matrix Bool Bool ℂ) (b : Bool) :
    holevoMap R (fun b : Bool => pureDensity (ket b)) (pureDensity (ket b)) = R b := by
  cases b <;> ext i j <;>
    simp [holevoMap,pureDensity,ket,Matrix.mul_apply,Matrix.trace,Fintype.sum_bool]

private lemma ket_psd (b : Bool) : (pureDensity (ket b)).PosSemidef := by
  have he : pureDensity (ket b) = Matrix.diagonal (fun c : Bool => if c = b then (1 : ℂ) else 0) := by
    ext i j
    cases b <;> cases i <;> cases j <;> simp [pureDensity,ket]
  rw [he]
  exact Matrix.PosSemidef.diagonal (by intro i; change 0 ≤ if i = b then (1 : ℂ) else 0; split_ifs <;> norm_num)

private lemma cp_positive (Phi : QMap) (hp : IsCompletelyPositive Phi)
    (X : Matrix Bool Bool ℂ) (hX : X.PosSemidef) : (Phi X).PosSemidef := by
  let Y : Matrix (Fin 1 × Bool) (Fin 1 × Bool) ℂ := X.submatrix Prod.snd Prod.snd
  have hy : Y.PosSemidef := hX.submatrix Prod.snd
  have ho := (hp 1 Y hy).submatrix (fun b => (0,b))
  exact ho

private lemma cq_cpt (R : Bool → Matrix Bool Bool ℂ)
    (hR : ∀ b, IsDensityMatrix (R b)) :
    CPT (holevoMap R (fun b : Bool => pureDensity (ket b))) := by
  constructor
  · intro X
    change (∑ b : Bool, (pureDensity (ket b) * X).trace • R b).trace = X.trace
    rw [Matrix.trace_sum]
    have ht : ∀ b, (R b).trace = 1 := fun b => (hR b).2
    simp only [Matrix.trace_smul,ht,mul_one]
    simp [Matrix.trace,Matrix.mul_apply,Fintype.sum_bool,pureDensity,ket]
  · intro r X hX
    have he : idTensorSuperop (holevoMap R (fun b : Bool => pureDensity (ket b))) X =
        ∑ b : Bool, Matrix.kronecker (X.submatrix (fun i => (i,b)) (fun i => (i,b))) (R b) := by
      ext i j
      simp [idTensorSuperop,holevoMap,Matrix.mul_apply,Matrix.trace,Fintype.sum_bool,
        pureDensity,ket,Matrix.kronecker_apply]
    rw [he]
    exact Matrix.posSemidef_sum Finset.univ (fun b _ => (hX.submatrix _).kronecker (hR b).1)

theorem solution (t : Bloch) (a : ℝ) :
    (CPT (canonical t ![0,0,a]) ↔ t 0^2+t 1^2+(|t 2|+|a|)^2 ≤ 1) ∧
    (CPT (canonical t ![0,0,a]) → IsCQMap (canonical t ![0,0,a]) ∧
      canonical t ![0,0,a] = holevoMap
        (fun b : Bool => blochDensity (t + Pi.single 2 (if b then -a else a)))
        (fun b : Bool => pureDensity (ket b))) := by
  have equivalence : CPT (canonical t ![0,0,a]) ↔
      ∀ b : Bool, IsDensityMatrix (blochDensity (t + Pi.single 2 (if b then -a else a))) := by
    constructor
    · intro h b
      have he := linear_formula t a
      rw [he] at h
      have hp := cp_positive _ h.2 _ (ket_psd b)
      rw [output_on_ket] at hp
      refine ⟨hp,?_⟩
      rw [bloch_entries]
      simp [Matrix.trace,Fintype.sum_bool]
      push_cast
      ring
    · intro h
      rw [linear_formula]
      exact cq_cpt _ h
  have bound : (∀ b : Bool, IsDensityMatrix (blochDensity (t + Pi.single 2 (if b then -a else a)))) ↔
      t 0^2+t 1^2+(|t 2|+|a|)^2 ≤ 1 := by
    constructor
    · intro h
      have hp := bloch_bound _ (h false).1
      have hm := bloch_bound _ (h true).1
      simp [Pi.single_apply] at hp hm
      rcases le_total 0 (t 2) with hz | hz <;> rcases le_total 0 a with ha | ha
      · simpa [abs_of_nonneg hz,abs_of_nonneg ha] using hp
      · simpa [abs_of_nonneg hz,abs_of_nonpos ha,sub_eq_add_neg] using hm
      · simp only [abs_of_nonpos hz,abs_of_nonneg ha]
        nlinarith
      · simp only [abs_of_nonpos hz,abs_of_nonpos ha]
        nlinarith
    · intro h b
      apply bloch_density
      have hplus : (t 2 + a)^2 ≤ (|t 2|+|a|)^2 := by
        nlinarith [abs_le.mp (abs_add_le (t 2) a),sq_abs (t 2 + a)]
      have hminus : (t 2 - a)^2 ≤ (|t 2|+|a|)^2 := by
        nlinarith [abs_le.mp (abs_sub (t 2) a),sq_abs (t 2 - a)]
      cases b <;> simp [Pi.single_apply] <;> nlinarith
  refine ⟨equivalence.trans bound,?_⟩
  intro h
  refine ⟨?_,linear_formula t a⟩
  refine ⟨1,_,equivalence.mp h,?_⟩
  simpa [act] using linear_formula t a
