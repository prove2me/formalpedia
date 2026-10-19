-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P08.trulyPlanar
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:30:11.876572+00:00
-- url     : https://prove2.me/submissions/918fcd8f-935b-4962-a397-fd05b304d0cc

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P08_Model
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder ComplexConjugate Kronecker
open QAlgorithms QAlgorithms.Entanglement QAlgorithms.QubitChannels
open QAlgorithms.Papers.Independent.Independent1.P08

private lemma cp_comp (F G : QMap) (hF : IsCompletelyPositive F)
    (hG : IsCompletelyPositive G) : IsCompletelyPositive (F.comp G) := by
  intro r X hX
  exact hF r _ (hG r X hX)

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

private lemma bell_entries (i j k l : Bool) :
    pureDensity bell (i,j) (k,l) = if i = j ∧ k = l then (1/2 : ℂ) else 0 := by
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1/2 : ℝ) := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt (by norm_num)]
    norm_num
  cases i <;> cases j <;> cases k <;> cases l <;>
    norm_num [pureDensity,bell,finiteMaxEntangled] <;> simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat] using congrArg Complex.ofReal hr

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


private def planarQ (t lam : Bloch) : Matrix Bool Bool ℂ :=
  let A := 1 - (t 0)^2 - (t 1)^2 - (t 2)^2
  Matrix.of fun i j => if i then
    (if j then ((A-(lam 0+lam 1)^2 : ℝ) : ℂ)
    else -2*((t 0 : ℂ)*(lam 0 : ℂ)-Complex.I*(t 1 : ℂ)*(lam 1 : ℂ)))
    else (if j then -2*((t 0 : ℂ)*(lam 0 : ℂ)+Complex.I*(t 1 : ℂ)*(lam 1 : ℂ))
      else ((A-(lam 0-lam 1)^2 : ℝ) : ℂ))

private def planarB (t lam : Bloch) : Matrix Bool Bool ℂ :=
  fun i j => if i = j then (t 0 : ℂ)-Complex.I*(t 1 : ℂ)
    else if i then (lam 0 : ℂ)-(lam 1 : ℂ) else (lam 0 : ℂ)+(lam 1 : ℂ)

private def planarC (t lam : Bloch) : Matrix (Bool × Bool) Bool ℂ :=
  fun p k => if p.2 then (1+(t 2 : ℂ)) * (if p.1 = k then 1 else 0)
    else -planarB t lam p.1 k

-- A polynomial Schur-complement congruence avoids inverses and boundary assumptions.
private lemma planar_congruence (t lam : Bloch) (hz : lam 2 = 0) :
    (planarC t lam)ᴴ * ((4 : ℂ) • choiState (canonical t lam)) * planarC t lam =
      ((1+t 2 : ℝ) : ℂ) • planarQ t lam := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
      planarC, planarB, planarQ, choiState, idTensorSuperop, canonical_entries,
      bell_entries, hz] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

private lemma planarQ_positive (t lam : Bloch) (hz : lam 2 = 0)
    (ht : 0 < 1+t 2) (h : IsCompletelyPositive (canonical t lam)) :
    (planarQ t lam).PosSemidef := by
  have hp := ((choi_positive _ h).smul (by norm_num : (0 : ℂ) ≤ 4)).conjTranspose_mul_mul_same (planarC t lam)
  rw [planar_congruence t lam hz] at hp
  have hh := hp.smul (by exact_mod_cast inv_nonneg.mpr ht.le : (0 : ℂ) ≤ ((1+t 2 : ℝ)⁻¹ : ℂ))
  simpa only [smul_smul, Complex.ofReal_inv, inv_mul_cancel₀ (by exact_mod_cast ne_of_gt ht : ((1+t 2 : ℝ) : ℂ) ≠ 0), one_smul] using hh

private lemma planarQ_inequalities (t lam : Bloch) (h : (planarQ t lam).PosSemidef) :
    0 ≤ 1-t 0^2-t 1^2-t 2^2-(lam 0-lam 1)^2 ∧
    0 ≤ 1-t 0^2-t 1^2-t 2^2-(lam 0+lam 1)^2 ∧
    4*((t 0*lam 0)^2+(t 1*lam 1)^2) ≤
      (1-t 0^2-t 1^2-t 2^2-(lam 0-lam 1)^2)*
      (1-t 0^2-t 1^2-t 2^2-(lam 0+lam 1)^2) := by
  have ha := (Complex.nonneg_iff.mp (h.diag_nonneg (i := false))).1
  have hd := (Complex.nonneg_iff.mp (h.diag_nonneg (i := true))).1
  have ht := (Complex.nonneg_iff.mp (h.submatrix finTwoEquiv).det_nonneg).1
  simp [planarQ, pow_two, Complex.mul_re] at ha hd
  refine ⟨by linarith only [ha], by linarith only [hd], ?_⟩
  simp [planarQ, Matrix.det_fin_two, Matrix.submatrix_apply, finTwoEquiv,
    Complex.mul_re, Complex.mul_im, pow_two] at ht
  nlinarith only [ht]



private def planarBounds (t lam : Bloch) : Prop :=
    0 ≤ 1-t 0^2-t 1^2-t 2^2-(lam 0-lam 1)^2 ∧
    0 ≤ 1-t 0^2-t 1^2-t 2^2-(lam 0+lam 1)^2 ∧
    4*((t 0*lam 0)^2+(t 1*lam 1)^2) ≤
      (1-t 0^2-t 1^2-t 2^2-(lam 0-lam 1)^2)*
      (1-t 0^2-t 1^2-t 2^2-(lam 0+lam 1)^2)

private lemma cp_flip (t lam : Bloch) (h : IsCompletelyPositive (canonical t lam)) :
    IsCompletelyPositive (canonical ![t 0,-t 1,-t 2] lam) := by
  have he : canonical ![t 0,-t 1,-t 2] lam =
      (sandwich pauliX).comp ((canonical t lam).comp (sandwich pauliX)) := by
    ext X i j
    cases i <;> cases j <;>
      simp [canonical_entries, sandwich, pauliX, Matrix.mul_apply,
        Matrix.conjTranspose_apply] <;> ring
  rw [he]
  exact cp_comp _ _ (cp_sandwich _) (cp_comp _ _ h (cp_sandwich _))

private lemma planar_bounds (t lam : Bloch) (hz : lam 2 = 0)
    (h : IsCompletelyPositive (canonical t lam)) : planarBounds t lam := by
  by_cases ht : 0 < 1+t 2
  · exact planarQ_inequalities t lam (planarQ_positive t lam hz ht h)
  · have hp := planarQ_inequalities ![t 0,-t 1,-t 2] lam
      (planarQ_positive _ lam hz (by simp; linarith) (cp_flip t lam h))
    simpa [planarBounds] using hp

private def cycleBloch (v : Bloch) : Bloch := ![v 2,v 0,v 1]

private def cycleMatrix : Matrix Bool Bool ℂ :=
  fun i j => if i then (if j then (1+Complex.I)/2 else (1-Complex.I)/2)
    else (if j then (-1-Complex.I)/2 else (1-Complex.I)/2)

set_option maxHeartbeats 800000 in
private lemma cp_cycle (t lam : Bloch) (h : IsCompletelyPositive (canonical t lam)) :
    IsCompletelyPositive (canonical (cycleBloch t) (cycleBloch lam)) := by
  have hI5 : Complex.I^5 = Complex.I := by rw [pow_succ, Complex.I_pow_four, one_mul]
  have he : canonical (cycleBloch t) (cycleBloch lam) =
      (sandwich cycleMatrix).comp ((canonical t lam).comp (sandwich cycleMatrixᴴ)) := by
    ext X i j
    cases i <;> cases j <;>
      simp [canonical_entries, cycleBloch, sandwich, cycleMatrix, Matrix.mul_apply,
        Matrix.conjTranspose_apply, map_ofNat] <;>
      ring_nf <;> norm_num [Complex.I_sq, map_ofNat, hI5] <;> ring
  rw [he]
  exact cp_comp _ _ (cp_sandwich _) (cp_comp _ _ h (cp_sandwich _))

private lemma scalar_planar (u v w x y : ℝ)
    (hm : 0 ≤ 1-u^2-v^2-w^2-(x-y)^2)
    (hp : 0 ≤ 1-u^2-v^2-w^2-(x+y)^2)
    (hd : 4*((u*x)^2+(v*y)^2) ≤
      (1-u^2-v^2-w^2-(x-y)^2)*(1-u^2-v^2-w^2-(x+y)^2)) :
    (|x|+|y|)^2+u^2+v^2+w^2 ≤ 1 ∧
    (x ≠ 0 → y ≠ 0 → (|x|+|y|)^2+u^2+v^2+w^2 = 1 → u = 0 ∧ v = 0) := by
  have hb : (|x|+|y|)^2+u^2+v^2+w^2 ≤ 1 := by
    rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hx,abs_of_nonneg hy]; nlinarith only [hp]
    · rw [abs_of_nonneg hx,abs_of_nonpos hy]; nlinarith only [hm]
    · rw [abs_of_nonpos hx,abs_of_nonneg hy]; nlinarith only [hm]
    · rw [abs_of_nonpos hx,abs_of_nonpos hy]; nlinarith only [hp]
  refine ⟨hb, ?_⟩
  intro hx hy he
  have hprod : (1-u^2-v^2-w^2-(x-y)^2)*(1-u^2-v^2-w^2-(x+y)^2) = 0 := by
    rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hx,abs_of_nonneg hy] at he
      have hz : 1-u^2-v^2-w^2-(x+y)^2 = 0 := by nlinarith only [he]
      rw [hz,mul_zero]
    · rw [abs_of_nonneg hx,abs_of_nonpos hy] at he
      have hz : 1-u^2-v^2-w^2-(x-y)^2 = 0 := by nlinarith only [he]
      rw [hz,zero_mul]
    · rw [abs_of_nonpos hx,abs_of_nonneg hy] at he
      have hz : 1-u^2-v^2-w^2-(x-y)^2 = 0 := by nlinarith only [he]
      rw [hz,zero_mul]
    · rw [abs_of_nonpos hx,abs_of_nonpos hy] at he
      have hz : 1-u^2-v^2-w^2-(x+y)^2 = 0 := by nlinarith only [he]
      rw [hz,mul_zero]
  rw [hprod] at hd
  have hu : u*x = 0 := by nlinarith [sq_nonneg (u*x),sq_nonneg (v*y)]
  have hv : v*y = 0 := by nlinarith [sq_nonneg (u*x),sq_nonneg (v*y)]
  exact ⟨(mul_eq_zero.mp hu).resolve_right hx, (mul_eq_zero.mp hv).resolve_right hy⟩

private lemma scalar_strict (u v w x y p q r : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hv : p^2+q^2+r^2 ≤ 1)
    (hm : 0 ≤ 1-u^2-v^2-w^2-(x-y)^2)
    (hp : 0 ≤ 1-u^2-v^2-w^2-(x+y)^2)
    (hd : 4*((u*x)^2+(v*y)^2) ≤
      (1-u^2-v^2-w^2-(x-y)^2)*(1-u^2-v^2-w^2-(x+y)^2)) :
    (u+x*p)^2+(v+y*q)^2+w^2 < 1 := by
  let S := 1-u^2-v^2-w^2-x^2-y^2
  have hS : 0 ≤ S := by dsimp [S]; nlinarith only [hm,hp]
  have hcs : (2*(u*x*p+v*y*q))^2 ≤ S^2 := by
    have h0 : 0 ≤ S^2-4*((u*x)^2+(v*y)^2) := by
      dsimp [S]; nlinarith [sq_nonneg (x*y)]
    have h1 := mul_nonneg h0 (by positivity : 0 ≤ p^2+q^2)
    have h2 := mul_nonneg (sq_nonneg S) (by nlinarith [sq_nonneg r] : 0 ≤ 1-(p^2+q^2))
    nlinarith [sq_nonneg (u*x*q-v*y*p)]
  have hlin : 2*(u*x*p+v*y*q) ≤ S := by
    exact le_of_sq_le_sq hcs hS
  have hp1 : 0 ≤ 1-p^2 := by nlinarith [sq_nonneg q,sq_nonneg r]
  have hq1 : 0 ≤ 1-q^2 := by nlinarith [sq_nonneg p,sq_nonneg r]
  have hsmall : x^2*p^2+y^2*q^2 < x^2+y^2 := by
    have hx2 : 0 < x^2 := sq_pos_of_ne_zero hx
    have hy2 : 0 < y^2 := sq_pos_of_ne_zero hy
    by_cases hz : p^2 = 1
    · have hq : q = 0 := by nlinarith [sq_nonneg q,sq_nonneg r]
      rw [hz,hq]; nlinarith only [hy2]
    · have hpos := mul_pos hx2 (lt_of_le_of_ne hp1 (by intro he; apply hz; linarith only [he]))
      have hnonneg := mul_nonneg (sq_nonneg y) hq1
      nlinarith only [hpos,hnonneg]
  dsimp [S] at hlin
  nlinarith only [hlin,hsmall]

private lemma norm_sq (v : Bloch) : blochNorm v^2 = v 0^2+v 1^2+v 2^2 := by
  rw [blochNorm, Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg (v j)))]
  simp [Fin.sum_univ_succ,add_assoc]

private lemma bloch_norm_nonneg (v : Bloch) : 0 ≤ blochNorm v := Real.sqrt_nonneg _

private lemma strict_zero_two (t lam v : Bloch) (hz : lam 2 = 0)
    (hx : lam 0 ≠ 0) (hy : lam 1 ≠ 0)
    (h : IsCompletelyPositive (canonical t lam)) (hv : blochNorm v ≤ 1) :
    blochNorm (t+fun j => lam j*v j) < 1 := by
  obtain ⟨hm,hp,hd⟩ := planar_bounds t lam hz h
  have hv2 : v 0^2+v 1^2+v 2^2 ≤ 1 := by
    rw [← norm_sq]
    simpa using (sq_le_sq₀ (bloch_norm_nonneg v) (by norm_num : (0 : ℝ) ≤ 1)).mpr hv
  have hs := scalar_strict (t 0) (t 1) (t 2) (lam 0) (lam 1)
    (v 0) (v 1) (v 2) hx hy hv2 hm hp hd
  have he := norm_sq (t+fun j => lam j*v j)
  simp [hz] at he
  nlinarith [bloch_norm_nonneg (t+fun j => lam j*v j)]

private lemma norm_cycle (v : Bloch) : blochNorm (cycleBloch v) = blochNorm v := by
  unfold blochNorm
  congr 1
  simp [cycleBloch,Fin.sum_univ_succ]
  ring

private lemma norm_cycle_affine (t lam v : Bloch) :
    blochNorm (cycleBloch t+fun j => cycleBloch lam j*cycleBloch v j) =
      blochNorm (t+fun j => lam j*v j) := by
  rw [← norm_cycle (t+fun j => lam j*v j)]
  congr 1
  ext i; fin_cases i <;> rfl

theorem solution (t lam : Bloch) (hPhi : CPT (canonical t lam)) :
    ((Finset.univ.filter fun j => lam j = 0).card = 1 →
      ∀ v : Bloch, blochNorm v ≤ 1 → blochNorm (t + fun j => lam j*v j) < 1) ∧
    (lam 2 = 0 → (|lam 0|+|lam 1|)^2+blochNorm t^2 ≤ 1) ∧
    (lam 2 = 0 → lam 0 ≠ 0 → lam 1 ≠ 0 →
      (|lam 0|+|lam 1|)^2+blochNorm t^2 = 1 → t 0 = 0 ∧ t 1 = 0) := by
  constructor
  · intro hcount v hv
    obtain ⟨j,hj⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter fun j => lam j = 0).card)
    have hz := (Finset.mem_filter.mp hj).2
    have hnot : ∀ k, k ≠ j → lam k ≠ 0 := by
      intro k hne hk
      have hsub : {j,k} ⊆ (Finset.univ.filter fun j => lam j = 0) := by
        intro a ha
        simp only [Finset.mem_insert,Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact hj
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩
      have hc := Finset.card_le_card hsub
      have hjk : j ≠ k := Ne.symm hne
      simp [hjk,hcount] at hc
    fin_cases j
    · have hh := strict_zero_two (cycleBloch (cycleBloch t)) (cycleBloch (cycleBloch lam))
        (cycleBloch (cycleBloch v)) (by simpa [cycleBloch] using hz)
        (by simpa [cycleBloch] using hnot 1 (by decide))
        (by simpa [cycleBloch] using hnot 2 (by decide))
        (cp_cycle _ _ (cp_cycle _ _ hPhi.2)) (by simpa only [norm_cycle] using hv)
      simpa only [norm_cycle_affine] using hh
    · have hh := strict_zero_two (cycleBloch t) (cycleBloch lam) (cycleBloch v)
        (by simpa [cycleBloch] using hz)
        (by simpa [cycleBloch] using hnot 2 (by decide))
        (by simpa [cycleBloch] using hnot 0 (by decide))
        (cp_cycle _ _ hPhi.2) (by simpa only [norm_cycle] using hv)
      simpa only [norm_cycle_affine] using hh
    · exact strict_zero_two t lam v hz (hnot 0 (by decide)) (hnot 1 (by decide)) hPhi.2 hv
  · constructor
    · intro hz
      obtain ⟨hm,hp,hd⟩ := planar_bounds t lam hz hPhi.2
      have hb := (scalar_planar (t 0) (t 1) (t 2) (lam 0) (lam 1) hm hp hd).1
      rw [norm_sq]
      linarith
    · intro hz hx hy he
      obtain ⟨hm,hp,hd⟩ := planar_bounds t lam hz hPhi.2
      apply (scalar_planar (t 0) (t 1) (t 2) (lam 0) (lam 1) hm hp hd).2 hx hy
      rw [norm_sq] at he
      linarith

#print axioms solution
