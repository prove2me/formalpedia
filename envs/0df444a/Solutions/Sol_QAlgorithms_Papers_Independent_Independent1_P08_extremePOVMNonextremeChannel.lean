-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P08.extremePOVMNonextremeChannel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:08:14.353321+00:00
-- url     : https://prove2.me/submissions/99499fa2-5e15-47d7-85b2-d599dd147783

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P08_Model
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped Matrix MatrixOrder ComplexOrder ComplexConjugate
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

private lemma bloch_bound (t : Bloch) (h : (blochDensity t).PosSemidef) :
    t 0^2+t 1^2+t 2^2 ≤ 1 := by
  have hd := (h.submatrix finTwoEquiv).det_nonneg
  rw [Matrix.det_fin_two] at hd
  apply Complex.nonneg_iff.mp at hd
  have hr := hd.1
  norm_num [Matrix.submatrix_apply,finTwoEquiv,bloch_entries,Complex.mul_re,
    Complex.mul_im,Complex.div_re,Complex.div_im] at hr
  nlinarith

private def coords (A : Matrix Bool Bool ℂ) : Bloch :=
  ![2*(A false true).re, -2*(A false true).im, 2*(A false false).re-1]

private lemma density_rep (A : Matrix Bool Bool ℂ) (hA : IsDensityMatrix A) :
    A = blochDensity (coords A) := by
  have hh := hA.1.isHermitian
  have h00 := congrArg Complex.im (congrFun (congrFun hh false) false)
  have h11 := congrArg Complex.im (congrFun (congrFun hh true) true)
  have h10 := congrFun (congrFun hh false) true
  have ht := congrArg Complex.re hA.2
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_bool, Complex.add_re,
    Complex.one_re] at ht
  simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_im] at h00 h11
  simp only [Matrix.conjTranspose_apply, Complex.star_def] at h10
  have hr10 := congrArg Complex.re h10
  have hi10 := congrArg Complex.im h10
  simp only [Complex.conj_re, Complex.conj_im] at hr10 hi10
  rw [bloch_entries]
  ext i j : 2
  cases i <;> cases j <;> apply Complex.ext <;>
    simp [coords, Complex.mul_re, Complex.mul_im] <;>
    linarith

private lemma sphere_extreme (t x y : Bloch) (ht : t 0^2+t 1^2+t 2^2=1)
    (hx : x 0^2+x 1^2+x 2^2≤1) (hy : y 0^2+y 1^2+y 2^2≤1)
    (a b : ℝ) (ha : 0<a) (hb : 0<b) (hab : a+b=1)
    (he : a • x + b • y = t) : x=t := by
  have he0 := congrFun he 0
  have he1 := congrFun he 1
  have he2 := congrFun he 2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at he0 he1 he2
  have hid : a*(x 0^2+x 1^2+x 2^2)+b*(y 0^2+y 1^2+y 2^2) -
      ((a*x 0+b*y 0)^2+(a*x 1+b*y 1)^2+(a*x 2+b*y 2)^2) =
      a*b*((x 0-y 0)^2+(x 1-y 1)^2+(x 2-y 2)^2) := by
    have hbval : b=1-a := by linarith
    rw [hbval]
    ring
  rw [he0,he1,he2,ht] at hid
  have hp : 0<a*b := mul_pos ha hb
  have hu : a*(x 0^2+x 1^2+x 2^2)+b*(y 0^2+y 1^2+y 2^2)≤1 := by
    nlinarith [mul_le_mul_of_nonneg_left hx ha.le,mul_le_mul_of_nonneg_left hy hb.le]
  have hz : (x 0-y 0)^2+(x 1-y 1)^2+(x 2-y 2)^2=0 := by
    nlinarith only [hid,hu,hp,sq_nonneg (x 0-y 0),sq_nonneg (x 1-y 1),sq_nonneg (x 2-y 2)]
  have h0 : x 0=y 0 := by nlinarith only [hz,sq_nonneg (x 0-y 0),sq_nonneg (x 1-y 1),sq_nonneg (x 2-y 2)]
  have h1 : x 1=y 1 := by nlinarith only [hz,sq_nonneg (x 0-y 0),sq_nonneg (x 1-y 1),sq_nonneg (x 2-y 2)]
  have h2 : x 2=y 2 := by nlinarith only [hz,sq_nonneg (x 0-y 0),sq_nonneg (x 1-y 1),sq_nonneg (x 2-y 2)]
  have hxy : x=y := by
    ext j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  rw [← hxy] at he
  simpa [← add_smul,hab] using he

private lemma density_extreme (t : Bloch) (ht : t 0^2+t 1^2+t 2^2=1)
    (A B : Matrix Bool Bool ℂ) (hA : IsDensityMatrix A) (hB : IsDensityMatrix B)
    (a b : ℝ) (ha : 0<a) (hb : 0<b) (hab : a+b=1)
    (he : a • A+b • B=blochDensity t) : A=blochDensity t := by
  have hca := bloch_bound (coords A) (by rw [← density_rep A hA]; exact hA.1)
  have hcb := bloch_bound (coords B) (by rw [← density_rep B hB]; exact hB.1)
  have hc : a • coords A+b • coords B=t := by
    have h00 := congrArg Complex.re (congrFun (congrFun he false) false)
    have h01 := congrArg Complex.re (congrFun (congrFun he false) true)
    have hi01 := congrArg Complex.im (congrFun (congrFun he false) true)
    simp [bloch_entries, Complex.real_smul, Complex.mul_re, Complex.mul_im] at h00 h01 hi01
    ext j
    fin_cases j <;> simp [coords] <;> linarith
  rw [density_rep A hA, sphere_extreme t _ _ ht hca hcb a b ha hb hab hc]

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

private lemma positive_ray (t : Bloch) (ht : t 0^2+t 1^2+t 2^2=1)
    (A B : Matrix Bool Bool ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (a b r : ℝ) (ha : 0<a) (hb : 0<b) (hr : 0<r)
    (he : a • A+b • B=r • blochDensity t) :
    ∃ c : ℝ, A=c • blochDensity t := by
  have hn (C : Matrix Bool Bool ℂ) (hC : C.PosSemidef) (hc : 0<C.trace.re) :
      IsDensityMatrix ((C.trace.re)⁻¹ • C) := by
    constructor
    · exact hC.smul (inv_nonneg.mpr hc.le)
    · rw [Matrix.trace_smul]
      have hcC : C.trace = (C.trace.re : ℂ) := Complex.ext rfl (by simpa using hC.trace_nonneg.2.symm)
      rw [hcC]
      simp [Complex.real_smul,ne_of_gt hc]
  have htR := (bloch_density t ht.le).2
  by_cases h0 : A.trace.re=0
  · have hz : A=0 := hA.trace_eq_zero_iff.mp (Complex.ext h0 (by simpa using hA.trace_nonneg.2.symm))
    exact ⟨0,by simp [hz]⟩
  have hap : 0<A.trace.re := lt_of_le_of_ne hA.trace_nonneg.1 (Ne.symm h0)
  by_cases h1 : B.trace.re=0
  · have hz : B=0 := hB.trace_eq_zero_iff.mp (Complex.ext h1 (by simpa using hB.trace_nonneg.2.symm))
    refine ⟨r/a,?_⟩
    have he' := congrArg (fun C : Matrix Bool Bool ℂ => a⁻¹ • C) he
    simpa [hz,smul_smul,ne_of_gt ha,div_eq_mul_inv,mul_comm] using he'
  have hbp : 0<B.trace.re := lt_of_le_of_ne hB.trace_nonneg.1 (Ne.symm h1)
  have htrace : a*A.trace.re+b*B.trace.re=r := by
    have h := congrArg (fun C : Matrix Bool Bool ℂ => C.trace.re) he
    simpa [Matrix.trace_add,Matrix.trace_smul,Complex.real_smul,htR] using h
  have he' : (a*A.trace.re/r) • ((A.trace.re)⁻¹ • A)+
      (b*B.trace.re/r) • ((B.trace.re)⁻¹ • B)=blochDensity t := by
    have h := congrArg (fun C : Matrix Bool Bool ℂ => r⁻¹ • C) he
    convert h using 1 <;> simp [smul_add,smul_smul,ne_of_gt hr,
      ne_of_gt hap,ne_of_gt hbp,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]
  have hd := density_extreme t ht _ _ (hn A hA hap) (hn B hB hbp)
    (a*A.trace.re/r) (b*B.trace.re/r) (div_pos (mul_pos ha hap) hr)
    (div_pos (mul_pos hb hbp) hr) (by rw [← add_div,htrace]; exact div_self (ne_of_gt hr)) he'
  refine ⟨A.trace.re,?_⟩
  have h := congrArg (fun C : Matrix Bool Bool ℂ => A.trace.re • C) hd
  simpa [smul_smul,ne_of_gt hap] using h

private lemma trine_unit (k : Fin 3) :
    trineVector k 0^2+trineVector k 1^2+trineVector k 2^2=1 := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  fin_cases k <;> norm_num [trineVector,Matrix.cons_val_two] <;> nlinarith

private lemma trine_scale (k : Fin 3) :
    trineEffect k=(2/3 : ℝ) • blochDensity (trineVector k) := by
  ext i j
  simp [trineEffect,blochDensity,Matrix.smul_apply,Complex.real_smul]
  ring

private lemma trine_povm : IsPOVM trineEffect := by
  constructor
  · intro k
    rw [trine_scale]
    exact (bloch_density _ (trine_unit k).le).1.smul (by norm_num)
  · ext i j
    cases i <;> cases j <;>
      norm_num [trineEffect,trineVector,sigma,pauliX,pauliY,pauliZ,Fin.sum_univ_succ] <;> ring

private lemma trine_povm_extreme :
    trineEffect ∈ ({F : Fin 3 → Matrix Bool Bool ℂ | IsPOVM F}).extremePoints ℝ := by
  refine ⟨trine_povm,?_⟩
  intro F hF G hG hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  have hray (k : Fin 3) : ∃ c : ℝ, F k=c • blochDensity (trineVector k) := by
    apply positive_ray _ (trine_unit k) _ _ (hF.1 k) (hG.1 k) a b (2/3)
      ha hb (by norm_num)
    simpa only [Pi.add_apply,Pi.smul_apply,← trine_scale] using congrFun he k
  choose c hc using hray
  have hs : ∑ k, c k • blochDensity (trineVector k)=(1 : Matrix Bool Bool ℂ) := by
    simpa only [← hc] using hF.2
  have h00 := congrArg Complex.re (congrFun (congrFun hs false) false)
  have h11 := congrArg Complex.re (congrFun (congrFun hs true) true)
  have h01 := congrArg Complex.re (congrFun (congrFun hs false) true)
  norm_num [bloch_entries,trineVector,Fin.sum_univ_succ,Complex.real_smul,Matrix.cons_val_two] at h00 h11 h01
  have hs3 : 0<Real.sqrt (3:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have h12 : c 1=c 2 := by nlinarith only [h00,h11,hs3]
  have h0 : c 0=2/3 := by linarith
  have h1 : c 1=2/3 := by linarith
  have h2 : c 2=2/3 := by linarith
  funext k
  rw [hc,trine_scale]
  have hk : c k=2/3 := by
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
  rw [hk]

private lemma trine_outputs (k : Fin 3) : IsDensityMatrix (trineOutput k) := by
  have h : trineOutput k=blochDensity (Pi.single k 1) := by
    simp [trineOutput,blochDensity]
  rw [h]
  apply bloch_density
  fin_cases k <;> norm_num [Pi.single_apply,Fin.ext_iff]

private lemma trine_eb : EBT trineChannel :=
  holevo_eb _ _ trine_outputs trine_povm

private lemma trine_not_point : ¬ IsPoint trineChannel := by
  rintro ⟨R,hR,he⟩
  have h := congrArg (fun A : Matrix Bool Bool ℂ => (A false true).im) (he (sigma 0))
  norm_num [trineChannel,holevoMap,trineEffect,trineOutput,trineVector,
    sigma,pauliX,pauliY,pauliZ,Fin.sum_univ_succ,Matrix.mul_apply,Matrix.trace,Matrix.cons_val_two] at h

private lemma unitary_projectors_sum (U : Matrix.unitaryGroup Bool ℂ) :
    ∑ b : Bool, pureDensity (act (U : Matrix Bool Bool ℂ) (ket b))=1 := by
  have hu := Matrix.mem_unitaryGroup_iff.mp U.property
  convert hu using 1
  ext i j
  simp [pureDensity,act,ket,Matrix.mul_apply]

private lemma cq_commute (Phi : QMap) (hPhi : IsCQMap Phi)
    (X Y : Matrix Bool Bool ℂ) (hx : X.trace=0) (hy : Y.trace=0) :
    Phi X * Phi Y=Phi Y * Phi X := by
  obtain ⟨U,R,hR,rfl⟩ := hPhi
  let F := fun b => pureDensity (act (U : Matrix Bool Bool ℂ) (ket b))
  have hf : F false+F true=1 := by
    simpa only [Fintype.sum_bool,add_comm] using unitary_projectors_sum U
  have hz (Z : Matrix Bool Bool ℂ) (hZ : Z.trace=0) :
      (F true*Z).trace= -(F false*Z).trace := by
    have h : (F false*Z).trace+(F true*Z).trace=0 := by
      rw [← Matrix.trace_add,← Matrix.add_mul,hf,Matrix.one_mul,hZ]
    linear_combination h
  have hformula (Z : Matrix Bool Bool ℂ) (hZ : Z.trace=0) :
      holevoMap R F Z=(F false*Z).trace • (R false-R true) := by
    simp [holevoMap,hz Z hZ,sub_eq_add_neg,add_comm]
  change holevoMap R F X * holevoMap R F Y=holevoMap R F Y * holevoMap R F X
  rw [hformula X hx,hformula Y hy]
  simp [smul_smul,mul_comm]

private lemma trine_not_cq : ¬ IsCQMap trineChannel := by
  intro h
  have hx : (sigma 0).trace=0 := by norm_num [sigma,pauliX,Matrix.trace]
  have hz : (sigma 2).trace=0 := by norm_num [sigma,pauliZ,Matrix.trace,Matrix.cons_val_two]
  have hc := cq_commute _ h _ _ hx hz
  have he := congrArg (fun A : Matrix Bool Bool ℂ => (A false true).im) hc
  norm_num [trineChannel,holevoMap,trineEffect,trineOutput,trineVector,
    sigma,pauliX,pauliY,pauliZ,Fin.sum_univ_succ,Matrix.mul_apply,Matrix.trace,Matrix.cons_val_two] at he
  have hs : 0<Real.sqrt (3:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  nlinarith only [he,hs]

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

private def rx : Fin 2 → Matrix Bool Bool ℂ :=
  ![blochDensity ![1,0,0],blochDensity ![-1/3,2/3,2/3]]

private def rz : Fin 2 → Matrix Bool Bool ℂ :=
  ![blochDensity ![1/3,(1+Real.sqrt 3)/3,(1-Real.sqrt 3)/3],
    blochDensity ![1/3,(1-Real.sqrt 3)/3,(1+Real.sqrt 3)/3]]

private def fx : QMap := holevoMap rx (pairPOVM 0)
private def fz : QMap := holevoMap rz (pairPOVM 2)

private lemma rx_density (k : Fin 2) : IsDensityMatrix (rx k) := by
  fin_cases k <;> apply bloch_density <;> norm_num [Matrix.cons_val_two]

private lemma rz_density (k : Fin 2) : IsDensityMatrix (rz k) := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  fin_cases k <;> apply bloch_density <;> norm_num [Matrix.cons_val_two] <;> nlinarith only [hs]

private lemma trine_midpoint : (1/2 : ℝ) • fx+(1/2 : ℝ) • fz=trineChannel := by
  apply LinearMap.ext
  intro X
  ext i j
  cases i <;> cases j <;>
    norm_num [fx,fz,rx,rz,pairPOVM,axis,trineChannel,holevoMap,trineEffect,trineOutput,
      trineVector,bloch_entries,sigma,pauliX,pauliY,pauliZ,Fin.sum_univ_succ,
      Matrix.mul_apply,Matrix.trace,Matrix.cons_val_two,Complex.real_smul] <;> ring

private lemma fx_ne_trine : fx≠trineChannel := by
  intro h
  have he := congrArg (fun F : QMap => (F (sigma 0) false true).im) h
  norm_num [fx,rx,pairPOVM,axis,trineChannel,holevoMap,trineEffect,trineOutput,
    trineVector,bloch_entries,sigma,pauliX,pauliY,pauliZ,Fin.sum_univ_succ,
    Matrix.mul_apply,Matrix.trace,Matrix.cons_val_two,Complex.real_smul] at he

private lemma trine_not_extreme : trineChannel ∉ ebtSet.extremePoints ℝ := by
  intro h
  have hx : fx ∈ ebtSet := holevo_eb _ _ rx_density (pair_povm 0)
  have hz : fz ∈ ebtSet := holevo_eb _ _ rz_density (pair_povm 2)
  apply fx_ne_trine
  exact h.2 hx hz ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,trine_midpoint⟩

theorem solution :
    trineEffect ∈ ({F : Fin 3 → Matrix Bool Bool ℂ | IsPOVM F}).extremePoints ℝ ∧
    (∀ k, IsDensityMatrix (trineOutput k)) ∧ EBT trineChannel ∧
    ¬ IsCQMap trineChannel ∧ ¬ IsPoint trineChannel ∧
    trineChannel ∉ ebtSet.extremePoints ℝ := by
  exact ⟨trine_povm_extreme,trine_outputs,trine_eb,trine_not_cq,trine_not_point,trine_not_extreme⟩

#print axioms solution
