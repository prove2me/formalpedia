-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P08.theorem4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:27:07.436916+00:00
-- url     : https://prove2.me/submissions/4c7fc91e-b94a-4072-9e9d-40c2beac409e

import Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_theorem3
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P08_Model
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped Matrix MatrixOrder ComplexOrder ComplexConjugate
open QAlgorithms QAlgorithms.Entanglement QAlgorithms.QubitChannels
open QAlgorithms.Papers.Independent.Independent1.P08

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

private lemma unitary_trace {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix.unitaryGroup I ℂ) (X : Matrix I I ℂ) :
    (conjSuperop (U : Matrix I I ℂ) X).trace = X.trace := by
  have hu : (U : Matrix I I ℂ)ᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp U.property
  rw [conjSuperop, Matrix.trace_mul_cycle, hu, Matrix.one_mul]

private lemma unitary_density {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix.unitaryGroup I ℂ) {X : Matrix I I ℂ} (hX : IsDensityMatrix X) :
    IsDensityMatrix (conjSuperop (U : Matrix I I ℂ) X) :=
  ⟨hX.1.mul_mul_conjTranspose_same _, (unitary_trace U X).trans hX.2⟩

private lemma tensor_sandwich {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (K : Matrix J J ℂ) (X : Matrix (I × J) (I × J) ℂ) :
    idTensorSuperop (conjSuperop K) X =
      Matrix.kronecker (1 : Matrix I I ℂ) K * X *
        (Matrix.kronecker (1 : Matrix I I ℂ) K)ᴴ := by
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker']
  ext p q
  simp [idTensorSuperop, conjSuperop, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, Matrix.one_apply]

private lemma tensor_unitary_density {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix.unitaryGroup Bool ℂ) {X : Matrix (I × Bool) (I × Bool) ℂ}
    (hX : IsDensityMatrix X) :
    IsDensityMatrix (idTensorSuperop (conjSuperop (U : Matrix Bool Bool ℂ)) X) := by
  constructor
  · rw [tensor_sandwich]
    exact hX.1.mul_mul_conjTranspose_same _
  · change (∑ i, _) = 1
    simp only [Matrix.diag, Fintype.sum_prod_type,
      idTensorSuperop, Matrix.of_apply]
    change (∑ i, (conjSuperop (U : Matrix Bool Bool ℂ)
      (X.submatrix (fun b => (i,b)) (fun b => (i,b)))).trace) = 1
    simp_rw [unitary_trace]
    simpa [Matrix.trace, Fintype.sum_prod_type] using hX.2

private lemma tensor_unitary_sep {I : Type*} [Fintype I] [Nonempty I]
    (U : Matrix.unitaryGroup Bool ℂ) {X : Matrix (I × Bool) (I × Bool) ℂ}
    (hX : IsSeparableDensity X) :
    IsSeparableDensity (idTensorSuperop (conjSuperop (U : Matrix Bool Bool ℂ)) X) := by
  obtain ⟨q,w,A,B,hw,hs,hAB,rfl⟩ := hX
  refine ⟨q,w,A,fun k => conjSuperop (U : Matrix Bool Bool ℂ) (B k),hw,hs,
    fun k => ⟨(hAB k).1,unitary_density U (hAB k).2⟩,?_⟩
  ext p r
  simp [idTensorSuperop, conjSuperop, Matrix.sum_apply, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_comm, mul_assoc, mul_left_comm,
    Matrix.kronecker]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private lemma change_eb (Phi : QMap) (U V : Matrix.unitaryGroup Bool ℂ)
    (h : EBT Phi) : EBT (changeBases U V Phi) := by
  constructor
  · intro X
    exact (unitary_trace V _).trans ((h.1 _).trans (unitary_trace U X))
  · intro a ha
    let : Nonempty (Fin a) := ⟨⟨0,ha⟩⟩
    intro X hX
    have hs := h.2 a ha _ (tensor_unitary_density U hX)
    have he : idTensorSuperop (changeBases U V Phi) X =
        idTensorSuperop (conjSuperop (V : Matrix Bool Bool ℂ))
          (idTensorSuperop Phi (idTensorSuperop (conjSuperop (U : Matrix Bool Bool ℂ)) X)) := rfl
    rw [he]
    exact tensor_unitary_sep V hs

private lemma unitary_cancel (U : Matrix.unitaryGroup Bool ℂ) (X : Matrix Bool Bool ℂ) :
    conjSuperop (star (U : Matrix Bool Bool ℂ)) (conjSuperop (U : Matrix Bool Bool ℂ) X) = X := by
  have h : (U : Matrix Bool Bool ℂ)ᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp U.property
  simp only [conjSuperop, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  simp only [← Matrix.mul_assoc, h, Matrix.one_mul]
  rw [Matrix.mul_assoc, h, Matrix.mul_one]

private lemma unitary_cancel' (U : Matrix.unitaryGroup Bool ℂ) (X : Matrix Bool Bool ℂ) :
    conjSuperop (U : Matrix Bool Bool ℂ) (conjSuperop (star (U : Matrix Bool Bool ℂ)) X) = X := by
  have h := unitary_cancel (star U) X
  simpa only [Unitary.coe_star, star_star] using h

private lemma change_eb_iff (Phi : QMap) (U V : Matrix.unitaryGroup Bool ℂ) :
    EBT (changeBases U V Phi) ↔ EBT Phi := by
  refine ⟨fun h => ?_, change_eb Phi U V⟩
  have hh := change_eb (changeBases U V Phi) (star U) (star V) h
  have he : changeBases (star U) (star V) (changeBases U V Phi) = Phi := by
    apply LinearMap.ext
    intro X
    change conjSuperop (star (V : Matrix Bool Bool ℂ))
      (conjSuperop (V : Matrix Bool Bool ℂ)
        (Phi (conjSuperop (U : Matrix Bool Bool ℂ)
          (conjSuperop (star (U : Matrix Bool Bool ℂ)) X)))) = Phi X
    rw [unitary_cancel', unitary_cancel]
  rwa [he] at hh

private def axis (j : Fin 3) (b : Bool) : Matrix Bool Bool ℂ :=
  (1/2 : ℂ) • (1 + (if b then (1 : ℂ) else -1) • sigma j)

private lemma axis_density (j : Fin 3) (b : Bool) : IsDensityMatrix (axis j b) := by
  have he : axis j b * (axis j b)ᴴ = axis j b := by
    ext x y
    fin_cases j <;> cases b <;> cases x <;> cases y <;>
      norm_num [axis, sigma, pauliX, pauliY, pauliZ, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Complex.I_sq, map_ofNat] <;> ring_nf <;> norm_num [Complex.I_sq]
  constructor
  · rw [← he]
    simpa using (Matrix.PosSemidef.one.mul_mul_conjTranspose_same (axis j b))
  · fin_cases j <;> cases b <;>
      norm_num [axis, sigma, pauliX, pauliY, pauliZ, Matrix.trace, Matrix.diag]

private def outStates : Fin 7 → Matrix Bool Bool ℂ :=
  ![(1/2 : ℂ) • 1, axis 0 true, axis 0 false,
    axis 1 true, axis 1 false, axis 2 true, axis 2 false]

private def pairEffect (j : Fin 3) (v : ℝ) (b : Bool) : Matrix Bool Bool ℂ :=
  (((|v|+v)/2 : ℝ) : ℂ) • axis j b + (((|v|-v)/2 : ℝ) : ℂ) • axis j (!b)

private def effects (lam : Bloch) : Fin 7 → Matrix Bool Bool ℂ :=
  ![((1 - ∑ j, |lam j| : ℝ) : ℂ) • 1,
    pairEffect 0 (lam 0) true, pairEffect 0 (lam 0) false,
    pairEffect 1 (lam 1) true, pairEffect 1 (lam 1) false,
    pairEffect 2 (lam 2) true, pairEffect 2 (lam 2) false]

private lemma output_states_density (k : Fin 7) : IsDensityMatrix (outStates k) := by
  fin_cases k
  · constructor
    · exact Matrix.PosSemidef.one.smul (by norm_num [Complex.nonneg_iff])
    · norm_num [outStates, Matrix.trace_smul, Matrix.trace_one]
  all_goals apply axis_density

private lemma pairEffect_psd (j : Fin 3) (v : ℝ) (b : Bool) : (pairEffect j v b).PosSemidef := by
  apply Matrix.PosSemidef.add
  · apply (axis_density j b).1.smul
    exact_mod_cast (show 0 ≤ (|v|+v)/2 by linarith [neg_abs_le v])
  · apply (axis_density j (!b)).1.smul
    exact_mod_cast (show 0 ≤ (|v|-v)/2 by linarith [le_abs_self v])

private lemma effects_povm (lam : Bloch) (h : ∑ j, |lam j| ≤ 1) : IsPOVM (effects lam) := by
  constructor
  · intro k
    fin_cases k
    · exact Matrix.PosSemidef.one.smul (by exact_mod_cast sub_nonneg.mpr h)
    all_goals exact pairEffect_psd _ _ _
  · ext x y
    cases x <;> cases y <;>
      norm_num [effects, pairEffect, axis, sigma, pauliX, pauliY, pauliZ, Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 800000 in
private lemma canonical_holevo (lam : Bloch) : canonical 0 lam = holevoMap outStates (effects lam) := by
  ext X x y
  cases x <;> cases y <;>
    norm_num [canonical, blochAffineMap, outStates, effects, pairEffect, axis, holevoMap,
      Matrix.mul_apply, Matrix.trace, Matrix.diag, Matrix.diagonal,
      sigma, pauliX, pauliY, pauliZ, Fin.sum_univ_succ] <;>
    ring_nf <;> norm_num [Complex.I_sq, Fin.ext_iff, Matrix.cons_val_two]

private lemma unitary_one (U : Matrix.unitaryGroup Bool ℂ) :
    conjSuperop (U : Matrix Bool Bool ℂ) 1 = 1 := by
  simpa [conjSuperop, Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp U.property

private lemma translation_zero (t lam : Bloch) (h : canonical t lam 1 = 1) : t = 0 := by
  have h00 := congrArg (fun A : Matrix Bool Bool ℂ => (A false false).re) h
  have h01 := congrArg (fun A : Matrix Bool Bool ℂ => (A false true).re) h
  have hi01 := congrArg (fun A : Matrix Bool Bool ℂ => (A false true).im) h
  norm_num [canonical, blochAffineMap, Matrix.mul_apply, Matrix.trace, Matrix.diag,
    Matrix.diagonal, sigma, pauliX, pauliY, pauliZ, Fin.sum_univ_succ] at h00 h01 hi01
  ext j
  fin_cases j
  · exact h01
  · exact hi01
  · exact h00

theorem solution (Phi : QMap) (_hPhi : CPT Phi) (hunital : Phi 1 = 1)
    (t lam : Bloch) (hcanonical : HasCanonicalRepresentation Phi t lam) :
    EBT Phi ↔ ∑ j, |lam j| ≤ 1 := by
  obtain ⟨U,V,hUV⟩ := hcanonical
  have he : Phi = changeBases U V (canonical t lam) := by
    apply LinearMap.ext
    exact hUV
  have ht : t = 0 := by
    apply translation_zero t lam
    have h := congrArg (conjSuperop (star (V : Matrix Bool Bool ℂ))) (hUV 1)
    rw [hunital,unitary_one,unitary_cancel] at h
    have hV := unitary_one (star V)
    change conjSuperop (star (V : Matrix Bool Bool ℂ)) 1 = 1 at hV
    rw [hV] at h
    exact h.symm
  rw [he,change_eb_iff]
  constructor
  · exact theorem3 t lam
  · intro hl
    rw [ht,canonical_holevo]
    exact holevo_eb _ _ output_states_density (effects_povm lam hl)

#print axioms solution
