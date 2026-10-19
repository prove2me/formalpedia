-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P08.purePointChannels
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:54:48.661982+00:00
-- url     : https://prove2.me/submissions/a6b17130-68dd-48e3-8ff8-6d7fc72ea2f8

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P08_Model
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Tactic

noncomputable section
open scoped Matrix ComplexOrder ComplexConjugate
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
    simp only [Matrix.trace_smul,ht]
    simp [Matrix.trace,Matrix.mul_apply,pureDensity,ket]
  · intro r X hX
    have he : idTensorSuperop (holevoMap R (fun b : Bool => pureDensity (ket b))) X =
        ∑ b : Bool, Matrix.kronecker (X.submatrix (fun i => (i,b)) (fun i => (i,b))) (R b) := by
      ext i j
      simp [idTensorSuperop,holevoMap,Matrix.mul_apply,Matrix.trace,
        pureDensity,ket]
    rw [he]
    exact Matrix.posSemidef_sum Finset.univ (fun b _ => (hX.submatrix _).kronecker (hR b).1)


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

private lemma point_formula (t : Bloch) (X : Matrix Bool Bool ℂ) :
    canonical t 0 X = X.trace • blochDensity t := by
  simp [canonical, blochAffineMap, blochDensity, smul_smul, div_eq_mul_inv]

private lemma point_cpt (t : Bloch) (h : IsDensityMatrix (blochDensity t)) :
    CPT (canonical t 0) ∧ IsCQMap (canonical t 0) := by
  have he : canonical t 0 = holevoMap (fun _ : Bool => blochDensity t)
      (fun b : Bool => pureDensity (ket b)) := by
    apply LinearMap.ext
    intro X
    rw [point_formula]
    ext i j
    simp [holevoMap, pureDensity, ket, Matrix.trace, Matrix.mul_apply]
    ring
  rw [he]
  refine ⟨cq_cpt _ (fun _ => h), 1, (fun _ => blochDensity t), (fun _ => h), ?_⟩
  simp [act]

private lemma point_eb (t : Bloch) (h : IsDensityMatrix (blochDensity t)) :
    EBT (canonical t 0) := by
  refine ⟨(point_cpt t h).1.1, ?_⟩
  intro r hr X hX
  let A : Matrix (Fin r) (Fin r) ℂ :=
    X.submatrix (fun i => (i,false)) (fun i => (i,false)) +
      X.submatrix (fun i => (i,true)) (fun i => (i,true))
  have hA : IsDensityMatrix A := by
    constructor
    · exact (hX.1.submatrix _).add (hX.1.submatrix _)
    · have ht := hX.2
      simpa [A, Matrix.trace, Matrix.diag, Fintype.sum_prod_type,
        Fintype.sum_bool, Finset.sum_add_distrib, add_comm] using ht
  refine ⟨1, fun _ => 1, fun _ => A, fun _ => blochDensity t,
    (by intro j; norm_num), (by simp), (fun _ => ⟨hA,h⟩), ?_⟩
  ext p q
  simp [idTensorSuperop, point_formula, A, Matrix.trace,
    add_mul,add_comm]

private def preservesDensities (F : QMap) : Prop :=
  ∀ X, IsDensityMatrix X → IsDensityMatrix (F X)

private lemma cpt_preserves (F : QMap) (h : CPT F) : preservesDensities F := by
  intro X hX
  exact ⟨cp_positive F h.2 X hX.1, (h.1 X).trans hX.2⟩

private lemma ebt_preserves (F : QMap) (h : EBT F) : preservesDensities F := by
  intro X hX
  let Y : Matrix (Fin 1 × Bool) (Fin 1 × Bool) ℂ := X.submatrix Prod.snd Prod.snd
  have hY : IsDensityMatrix Y := by
    refine ⟨hX.1.submatrix _, ?_⟩
    simpa [Y, Matrix.trace, Matrix.diag, Fintype.sum_prod_type] using hX.2
  obtain ⟨q,w,A,B,hw,_,hAB,he⟩ := h.2 1 (by norm_num) Y hY
  have hp : (idTensorSuperop F Y).PosSemidef := by
    rw [he]
    exact Matrix.posSemidef_sum _ fun j _ =>
      ((hAB j).1.1.kronecker (hAB j).2.1).smul (by exact_mod_cast hw j)
  exact ⟨hp.submatrix (fun b => ((0 : Fin 1),b)), (h.1 X).trans hX.2⟩

private lemma map_point_of_density (F : QMap) (t : Bloch)
    (h : ∀ X, IsDensityMatrix X → F X=blochDensity t) : F=canonical t 0 := by
  have h0 := h (blochDensity 0) (bloch_density 0 (by norm_num))
  have hj : ∀ j : Fin 3, F (blochDensity (Pi.single j 1))=blochDensity t := by
    intro j
    apply h
    apply bloch_density
    fin_cases j <;> norm_num [Pi.single_apply, Fin.ext_iff]
  apply LinearMap.ext
  intro X
  let c0 := X false true+X true false
  let c1 := Complex.I*(X false true-X true false)
  let c2 := X false false-X true true
  have hexp : X = (X.trace-c0-c1-c2) • blochDensity 0 +
      c0 • blochDensity (Pi.single 0 1) + c1 • blochDensity (Pi.single 1 1) +
      c2 • blochDensity (Pi.single 2 1) := by
    ext i j
    cases i <;> cases j <;>
      norm_num [bloch_entries, Pi.single_apply, c0, c1, c2, Matrix.trace, Fin.ext_iff] <;>
      ring_nf <;> norm_num [Complex.I_sq] <;> ring
  conv_lhs => rw [hexp]
  simp only [map_add, map_smul, h0, hj]
  rw [← add_smul, ← add_smul, ← add_smul, point_formula]
  congr 1
  ring

private lemma point_extreme (t : Bloch) (ht : t 0^2+t 1^2+t 2^2=1)
    (S : Set QMap) (hmem : canonical t 0 ∈ S)
    (hS : ∀ F ∈ S, preservesDensities F) : canonical t 0 ∈ S.extremePoints ℝ := by
  refine ⟨hmem, ?_⟩
  intro F hF G hG hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  apply map_point_of_density F t
  intro X hX
  apply density_extreme t ht (F X) (G X) (hS F hF X hX) (hS G hG X hX) a b ha hb hab
  have hh := LinearMap.congr_fun he X
  simpa [point_formula, hX.2] using hh

private lemma trace_pure (v : EuclideanSpace ℂ Bool) :
    (pureDensity v).trace = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  change (∑ i, v i * conj (v i)) = ((‖v‖ ^ 2 : ℝ) : ℂ)
  rw [EuclideanSpace.norm_sq_eq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private lemma pure_output (t : Bloch) (ht : t 0^2+t 1^2+t 2^2=1) :
    ∃ psi : EuclideanSpace ℂ Bool, IsState psi ∧ blochDensity t = pureDensity psi := by
  have hR := bloch_density t ht.le
  suffices hh : ∃ psi : EuclideanSpace ℂ Bool, blochDensity t = pureDensity psi by
    obtain ⟨psi,hpsi⟩ := hh
    refine ⟨psi,?_,hpsi⟩
    have htpsi : ‖psi‖^2=1 := by
      have hh := hR.2
      rw [hpsi,trace_pure] at hh
      exact_mod_cast hh
    change ‖psi‖=1
    nlinarith [norm_nonneg psi]
  have hz : -1 ≤ t 2 ∧ t 2 ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (t 0),sq_nonneg (t 1),sq_nonneg (t 2+1),sq_nonneg (t 2-1)]
  by_cases he : t 2 = -1
  · have hx : t 0=0 := by nlinarith [sq_nonneg (t 0),sq_nonneg (t 1)]
    have hy : t 1=0 := by nlinarith [sq_nonneg (t 0),sq_nonneg (t 1)]
    refine ⟨ket true,?_⟩
    ext i j
    cases i <;> cases j <;> norm_num [bloch_entries,he,hx,hy,pureDensity,ket]
  · let a : ℝ := Real.sqrt ((1+t 2)/2)
    have hap : 0<a := Real.sqrt_pos.mpr (by have hh := hz.1.lt_of_ne (Ne.symm he); linarith)
    have ha : a^2=(1+t 2)/2 := Real.sq_sqrt (by linarith)
    have haC : (a : ℂ)^2=((1+(t 2 : ℂ))/2) := by exact_mod_cast ha
    have htC : (t 0 : ℂ)^2+(t 1 : ℂ)^2+(t 2 : ℂ)^2=1 := by exact_mod_cast ht
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast hap.ne'
    let psi : EuclideanSpace ℂ Bool := WithLp.toLp 2
      (fun b => if b then ((t 0 : ℂ)+Complex.I*(t 1 : ℂ))/(2*(a : ℂ)) else (a : ℂ))
    refine ⟨psi,?_⟩
    have hc : (t 0 : ℂ)^2+(t 1 : ℂ)^2=2*(a : ℂ)^2*(1-(t 2 : ℂ)) := by
      linear_combination htC + 2*((t 2 : ℂ)-1)*haC
    ext i j
    cases i <;> cases j <;>
      simp [psi,pureDensity,bloch_entries,map_div₀,map_add,map_mul,map_ofNat] <;>
      field_simp [ha0] <;> ring_nf <;> norm_num [Complex.I_sq] <;>
      first | linear_combination -2*haC | linear_combination -hc

theorem solution (t : Bloch) (ht : blochNorm t ≤ 1) :
    CPT (canonical t 0) ∧ IsCQMap (canonical t 0) ∧ IsDensityMatrix (blochDensity t) ∧
    (∀ X, canonical t 0 X = X.trace • blochDensity t) ∧
    (blochNorm t = 1 →
      (∃ psi : EuclideanSpace ℂ Bool, IsState psi ∧ blochDensity t = pureDensity psi) ∧
      canonical t 0 ∈ cptSet.extremePoints ℝ ∧ canonical t 0 ∈ ebtSet.extremePoints ℝ) := by
  have hn : 0 ≤ ∑ j, t j^2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsq := Real.sq_sqrt hn
  have hs : t 0^2+t 1^2+t 2^2≤1 := by
    change Real.sqrt (∑ j, t j^2)≤1 at ht
    have hb : (∑ j, t j^2)≤1 := (Real.sqrt_le_one).mp ht
    simpa [Fin.sum_univ_succ,add_assoc] using hb
  have hR := bloch_density t hs
  refine ⟨(point_cpt t hR).1,(point_cpt t hR).2,hR,point_formula t,?_⟩
  intro he
  have heq : t 0^2+t 1^2+t 2^2=1 := by
    change Real.sqrt (∑ j, t j^2)=1 at he
    rw [he] at hsq
    simpa [Fin.sum_univ_succ,add_assoc] using hsq.symm
  refine ⟨pure_output t heq,?_,?_⟩
  · exact point_extreme t heq cptSet (point_cpt t hR).1 (fun F hF => cpt_preserves F hF)
  · exact point_extreme t heq ebtSet (point_eb t hR) (fun F hF => ebt_preserves F hF)

#print axioms solution
