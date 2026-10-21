-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P15.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T12:49:11.05591+00:00
-- url     : https://prove2.me/submissions/5607ceba-015f-4a8d-8a25-c6bf4e48103d

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15
noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction

open scoped MatrixOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15

namespace G59Q
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma tr_nonneg {P Q : Matrix I I ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) : 0 ≤ (P * Q).trace.re := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hQ
  rw [Matrix.nonneg_iff_posSemidef] at hP
  rw [Matrix.star_eq_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  exact (Complex.nonneg_iff.mp (hP.mul_mul_conjTranspose_same B).trace_nonneg).1

lemma tr_mono_right {X Y Z : Matrix I I ℂ} (hX : 0 ≤ X) (hYZ : Y ≤ Z) :
    (X * Y).trace.re ≤ (X * Z).trace.re := by
  have := tr_nonneg hX (sub_nonneg.2 hYZ)
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at this
  linarith

lemma tr_mono_left {X X' Y : Matrix I I ℂ} (hXX : X ≤ X') (hY : 0 ≤ Y) :
    (X * Y).trace.re ≤ (X' * Y).trace.re := by
  have := tr_nonneg (sub_nonneg.2 hXX) hY
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at this
  linarith

lemma rpow_eq {A : Matrix I I ℂ} (hA : 0 ≤ A) (s : ℝ) :
    QAlgorithms.Papers.Independent.Claimed50.P15.positiveMatrixRpow A s = A ^ s := by
  unfold QAlgorithms.Papers.Independent.Claimed50.P15.positiveMatrixRpow
  rw [CFC.rpow_eq_cfc_real hA]

lemma rpow_mul {A : Matrix I I ℂ} (hA : A.PosDef) (s : ℝ) : A ^ (1 - s) * A ^ s = A := by
  have hu : IsUnit A := hA.isStrictlyPositive.isUnit
  rw [← CFC.rpow_add hu, sub_add_cancel, CFC.rpow_one A hA.posSemidef.nonneg]


lemma parts (X : Matrix I I ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma traceNorm_herm {X : Matrix I I ℂ} (hX : X.IsHermitian) :
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

lemma audenaert (A B : Matrix I I ℂ) (hA : A.PosDef) (hB : B.PosDef) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (A.trace.re + B.trace.re - QAlgorithms.traceNorm (A - B)) / 2 ≤
      (A ^ (1 - s) * B ^ s).trace.re := by
  have hH : (A - B).IsHermitian := hA.isHermitian.sub hB.isHermitian
  set P := cfc (fun t : ℝ => max t 0) (A - B) with hP
  set Nn := cfc (fun t : ℝ => max (-t) 0) (A - B) with hN
  have hP0 : 0 ≤ P := cfc_nonneg (fun t _ => le_max_right _ _)
  have hN0 : 0 ≤ Nn := cfc_nonneg (fun t _ => le_max_right _ _)
  have hpn : P - Nn = A - B := parts _ hH
  rw [traceNorm_herm hH, ← hP, ← hN]
  have htr : A.trace.re - B.trace.re = P.trace.re - Nn.trace.re := by
    rw [← Complex.sub_re, ← Matrix.trace_sub, ← Complex.sub_re, ← Matrix.trace_sub, hpn]
  set C := B + P with hC
  have hCpd : C.PosDef := hB.add_posSemidef (Matrix.nonneg_iff_posSemidef.1 hP0)
  have hA0 : 0 ≤ A := hA.posSemidef.nonneg
  have hB0 : 0 ≤ B := hB.posSemidef.nonneg
  have hAC : A ≤ C := by
    have : A = B + P - Nn := by rw [add_sub_assoc, hpn]; abel
    rw [this, hC]; exact sub_le_self _ hN0
  have hBC : B ≤ C := le_add_of_nonneg_right hP0
  have hs1 : 1 - s ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have h1 : (A ^ (1 - s) * A ^ s).trace.re ≤ (A ^ (1 - s) * C ^ s).trace.re :=
    tr_mono_right CFC.rpow_nonneg (CFC.rpow_le_rpow hs hAC)
  have h2 : (A ^ (1 - s) * (C ^ s - B ^ s)).trace.re ≤ (C ^ (1 - s) * (C ^ s - B ^ s)).trace.re :=
    tr_mono_left (CFC.rpow_le_rpow hs1 hAC) (sub_nonneg.2 (CFC.rpow_le_rpow hs hBC))
  have h3 : (B ^ (1 - s) * B ^ s).trace.re ≤ (C ^ (1 - s) * B ^ s).trace.re :=
    tr_mono_left (CFC.rpow_le_rpow hs1 hBC) CFC.rpow_nonneg
  rw [rpow_mul hA] at h1
  rw [rpow_mul hB] at h3
  rw [Matrix.mul_sub, Matrix.mul_sub, rpow_mul hCpd, Matrix.trace_sub, Matrix.trace_sub,
    Complex.sub_re, Complex.sub_re] at h2
  have hCt : C.trace.re = B.trace.re + P.trace.re := by
    rw [hC, Matrix.trace_add, Complex.add_re]
  linarith

end G59Q

namespace G59R
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

lemma re_star_dot (v w : κ → ℂ) : (star w ⬝ᵥ v).re = (star v ⬝ᵥ w).re := by
  rw [Matrix.star_dotProduct]; simp

lemma quad (D : Matrix κ κ ℂ) (hD : D.PosDef) (v x : κ → ℂ) :
    (star v ⬝ᵥ ((D * (1 + D)⁻¹) *ᵥ v)).re ≤
      (star x ⬝ᵥ (D *ᵥ x)).re + (star (v - x) ⬝ᵥ (v - x)).re := by
  set M := 1 + D with hM
  have hMpd : M.PosDef := by
    rw [hM, add_comm]; exact hD.add_posSemidef Matrix.PosSemidef.one
  have hMu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1 hMpd.isUnit
  have hMH : Mᴴ = M := hMpd.isHermitian.eq
  have hMiH : (M⁻¹)ᴴ = M⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hMH]
  have hDM : D * M⁻¹ = 1 - M⁻¹ := by
    have : D = M - 1 := by rw [hM]; abel
    rw [this, Matrix.sub_mul, Matrix.mul_nonsing_inv _ hMu, Matrix.one_mul]
  set w := M⁻¹ *ᵥ v with hw
  have hMw : M *ᵥ w = v := by rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hMu, Matrix.one_mulVec]
  have hpos := hMpd.posSemidef.dotProduct_mulVec_nonneg (x - w)
  have hpos' : 0 ≤ (star (x - w) ⬝ᵥ (M *ᵥ (x - w))).re := (Complex.nonneg_iff.1 hpos).1
  have hswM : star w ᵥ* M = star v := by
    have h1 := Matrix.star_mulVec M w
    rw [hMH, hMw] at h1
    exact h1.symm
  have e1 : star (x - w) ⬝ᵥ (M *ᵥ (x - w)) =
      star x ⬝ᵥ (M *ᵥ x) - star x ⬝ᵥ v - star v ⬝ᵥ x + star w ⬝ᵥ v := by
    rw [star_sub, Matrix.mulVec_sub, hMw, sub_dotProduct, dotProduct_sub, dotProduct_sub,
      Matrix.dotProduct_mulVec (star w), hswM]
    ring
  rw [e1] at hpos'
  simp only [Complex.add_re, Complex.sub_re] at hpos'
  have e2 : (D * M⁻¹) *ᵥ v = v - w := by rw [hDM, Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [e2]
  have eMx : M *ᵥ x = x + D *ᵥ x := by rw [hM, Matrix.add_mulVec, Matrix.one_mulVec]
  rw [eMx, dotProduct_add] at hpos'
  have e3 : star (v - x) ⬝ᵥ (v - x) = star v ⬝ᵥ v - star v ⬝ᵥ x - star x ⬝ᵥ v + star x ⬝ᵥ x := by
    rw [star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]; ring
  rw [e3, dotProduct_sub]
  simp only [Complex.add_re, Complex.sub_re] at hpos' ⊢
  have := re_star_dot v w
  linarith

end G59R

namespace G59R
open QAlgorithms.Papers.Independent.Claimed50.P15
open scoped Kronecker
variable {I : Type*} [Fintype I] [DecidableEq I]

def vec (X : Matrix I I ℂ) : I × I → ℂ := fun p => X p.1 p.2

lemma vec_dot (X Y : Matrix I I ℂ) : star (vec X) ⬝ᵥ vec Y = (Xᴴ * Y).trace := by
  simp only [vec, dotProduct, Fintype.sum_prod_type, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Pi.star_apply]
  rw [Finset.sum_comm]

lemma modular_eq (nu omega : Matrix I I ℂ) :
    modularMatrix nu omega = nu ⊗ₖ (omega⁻¹)ᵀ := by
  ext p q; simp [modularMatrix, Matrix.kroneckerMap_apply]

lemma modular_mulVec (nu omega X : Matrix I I ℂ) :
    modularMatrix nu omega *ᵥ vec X = vec (nu * X * omega⁻¹) := by
  funext p
  simp only [modularMatrix, vec, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

end G59R


lemma g58d_parts {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma g58d_cfc_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma g58d_traceNorm_herm {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
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

lemma g58d_sqrt_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    cfc Real.sqrt A * cfc Real.sqrt A = A := by
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt A hA.nonneg]
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

lemma g58d_tr_psd_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  have hs : (cfc Real.sqrt A).IsHermitian := by
    have : (cfc Real.sqrt A).PosSemidef := by
      rw [← Matrix.nonneg_iff_posSemidef]; exact cfc_nonneg (fun x _ => Real.sqrt_nonneg x)
    exact this.1
  rw [← g58d_sqrt_sq hA, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h := hB.conjTranspose_mul_mul_same (cfc Real.sqrt A)
  rw [hs.eq] at h
  have := h.trace_nonneg
  rw [← Matrix.mul_assoc]
  exact (Complex.nonneg_iff.1 this).1

lemma g58d_tr_le_traceNorm {n : Type*} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) (h1 : (1 - X).PosSemidef) (h2 : (1 + X).PosSemidef) :
    (X * Y).trace.re ≤ QAlgorithms.traceNorm Y := by
  rw [g58d_traceNorm_herm hY]
  set P := cfc (fun t : ℝ => max t 0) Y
  set Q := cfc (fun t : ℝ => max (-t) 0) Y
  have hP : P.PosSemidef := g58d_cfc_psd Y _ (fun t => le_max_right _ _)
  have hQ : Q.PosSemidef := g58d_cfc_psd Y _ (fun t => le_max_right _ _)
  have hYPQ : Y = P - Q := (g58d_parts Y hY).symm
  have a1 := g58d_tr_psd_mul h1 hP
  have a2 := g58d_tr_psd_mul h2 hQ
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at a1
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.trace_add, Complex.add_re] at a2
  rw [hYPQ, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  linarith

lemma g58d_err {I : Type*} [Fintype I] [DecidableEq I] (nu omega T : Matrix I I ℂ) :
    testingError nu omega T = omega.trace.re - ((omega - nu) * T).trace.re := by
  simp only [testingError, evaluate, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.trace_sub,
    Complex.sub_re]
  ring

lemma g58d_proj_bound {I : Type*} [Fintype I] [DecidableEq I] {Y T : Matrix I I ℂ} (hY : Y.IsHermitian)
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
  have k := g58d_tr_le_traceNorm hY h1 h2
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re,
    Matrix.trace_mul_comm] at k
  simp at k
  linarith

theorem g58d_prop31 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (nu omega : Matrix I I ℂ) (hnu : nu.PosDef) (homega : omega.PosDef) :
    optimalError false nu omega = (testingError nu omega (positiveSupport (omega - nu)) : EReal) ∧
    (testingError nu omega (positiveSupport (omega - nu)) : EReal) =
      (((omega.trace.re + nu.trace.re - QAlgorithms.traceNorm (omega - nu)) / 2 : ℝ) : EReal) := by
  set Y := omega - nu with hYdef
  have hY : Y.IsHermitian := homega.1.sub hnu.1
  have hsa : IsSelfAdjoint Y := hY.isSelfAdjoint
  set P := positiveSupport Y with hPdef
  have hPpsd : P.PosSemidef := g58d_cfc_psd Y _ (fun t => by split_ifs <;> norm_num)
  have hPP : P * P = P := by
    rw [hPdef, positiveSupport, ← cfc_mul (fun x : ℝ => if 0 < x then (1:ℝ) else 0)
      (fun x : ℝ => if 0 < x then (1:ℝ) else 0) Y ((Matrix.finite_real_spectrum).continuousOn _)
      ((Matrix.finite_real_spectrum).continuousOn _)]
    apply cfc_congr; intro t _; dsimp only; split_ifs <;> norm_num
  have hYP : Y * P = cfc (fun t : ℝ => max t 0) Y := by
    rw [show Y * P = cfc (fun t : ℝ => t) Y * P from by rw [cfc_id' ℝ Y], hPdef, positiveSupport]
    rw [← cfc_mul (fun t : ℝ => t) (fun x : ℝ => if 0 < x then (1:ℝ) else 0) Y
      ((Matrix.finite_real_spectrum).continuousOn _) ((Matrix.finite_real_spectrum).continuousOn _)]
    apply cfc_congr; intro t _
    dsimp only
    split_ifs with h
    · simp [le_of_lt h]
    · simp [not_lt.mp h]
  have hval : testingError nu omega P = (omega.trace.re + nu.trace.re - QAlgorithms.traceNorm Y) / 2 := by
    rw [g58d_err, ← hYdef, hYP, g58d_traceNorm_herm hY]
    have hp := congrArg (fun M => M.trace.re) (g58d_parts Y hY)
    simp only [Matrix.trace_sub, Complex.sub_re] at hp
    rw [hYdef, Matrix.trace_sub, Complex.sub_re] at hp
    linarith
  have hlow : ∀ T, IsProjectionTest T →
      (omega.trace.re + nu.trace.re - QAlgorithms.traceNorm Y) / 2 ≤ testingError nu omega T := by
    intro T hT
    have := g58d_proj_bound hY hT.1 hT.2
    rw [g58d_err, ← hYdef]
    rw [hYdef, Matrix.trace_sub, Complex.sub_re] at this
    rw [← hYdef] at this
    linarith
  refine ⟨?_, by rw [hval]⟩
  apply le_antisymm
  · apply sInf_le
    exact ⟨P, by simpa [IsProjectionTest] using ⟨hPpsd.1, hPP⟩, rfl⟩
  · apply le_sInf
    rintro v ⟨T, hT, rfl⟩
    simp only [Bool.false_eq_true, if_false] at hT
    rw [hval]
    exact EReal.coe_le_coe_iff.mpr (hlow T hT)

open QAlgorithms.Papers.Independent.Claimed50.P15 in
lemma g59_sqrt {I : Type*} [Fintype I] [DecidableEq I] {omega : Matrix I I ℂ} (h : omega.PosDef) :
    (cfc Real.sqrt omega).IsHermitian ∧ cfc Real.sqrt omega * cfc Real.sqrt omega = omega := by
  have hsa : IsSelfAdjoint omega := h.isHermitian.isSelfAdjoint
  refine ⟨(cfc_predicate Real.sqrt omega : IsSelfAdjoint _).isHermitian, ?_⟩
  rw [← cfc_mul Real.sqrt Real.sqrt omega]
  conv_rhs => rw [← cfc_id' ℝ omega]
  apply cfc_congr
  intro x hx
  have : 0 ≤ x := spectrum_nonneg_of_nonneg h.posSemidef.nonneg hx
  exact Real.mul_self_sqrt this

open QAlgorithms.Papers.Independent.Claimed50.P15 in
lemma g59_lower {I : Type*} [Fintype I] [DecidableEq I]
    (nu omega : Matrix I I ℂ) (hnu : nu.PosDef) (homega : omega.PosDef)
    (T : Matrix I I ℂ) (hT : T.IsHermitian) (hTT : T * T = T) :
    resolventOverlap nu omega ≤ testingError nu omega T := by
  obtain ⟨hOH, hOO⟩ := g59_sqrt homega
  set Ω := cfc Real.sqrt omega with hΩ
  have hdetO : IsUnit Ω.det := by
    have : IsUnit (Ω * Ω).det := by
      rw [hOO]; exact (Matrix.isUnit_iff_isUnit_det _).1 homega.isUnit
    rw [Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  have hinv : omega⁻¹ = Ω⁻¹ * Ω⁻¹ := by rw [← hOO, Matrix.mul_inv_rev]
  have hO1 : Ω * omega⁻¹ * Ω = 1 := by
    rw [hinv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdetO, Matrix.one_mul,
      Matrix.nonsing_inv_mul _ hdetO]
  have hD : (modularMatrix nu omega).PosDef := by
    rw [G59R.modular_eq]; exact hnu.kronecker homega.inv.transpose
  have hq := G59R.quad _ hD (G59R.vec Ω) (G59R.vec (T * Ω))
  have hres : resolventOverlap nu omega =
      (star (G59R.vec Ω) ⬝ᵥ ((modularMatrix nu omega * (1 + modularMatrix nu omega)⁻¹) *ᵥ
        G59R.vec Ω)).re := rfl
  rw [← hres] at hq
  have hx : (star (G59R.vec (T * Ω)) ⬝ᵥ (modularMatrix nu omega *ᵥ G59R.vec (T * Ω))).re =
      (nu * T).trace.re := by
    rw [G59R.modular_mulVec, G59R.vec_dot, Matrix.conjTranspose_mul, hOH.eq, hT.eq]
    have e : Ω * T * (nu * (T * Ω) * omega⁻¹) = Ω * (T * nu * T * Ω * omega⁻¹) := by
      simp only [Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm]
    have e2 : T * nu * T * Ω * omega⁻¹ * Ω = T * (nu * T) * (Ω * omega⁻¹ * Ω) := by
      simp only [Matrix.mul_assoc]
    rw [e2, hO1, Matrix.mul_one, Matrix.trace_mul_comm, Matrix.mul_assoc, hTT]
  have hy : (star (G59R.vec Ω - G59R.vec (T * Ω)) ⬝ᵥ (G59R.vec Ω - G59R.vec (T * Ω))).re =
      (omega * (1 - T)).trace.re := by
    have ev : G59R.vec Ω - G59R.vec (T * Ω) = G59R.vec ((1 - T) * Ω) := by
      funext p; simp [G59R.vec, Matrix.sub_mul]
    rw [ev, G59R.vec_dot, Matrix.conjTranspose_mul, hOH.eq, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hT.eq]
    have hP : (1 - T) * (1 - T) = 1 - T := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hTT, sub_self, sub_zero]
    have e : Ω * (1 - T) * ((1 - T) * Ω) = Ω * ((1 - T) * (1 - T) * Ω) := by
      simp only [Matrix.mul_assoc]
    rw [e, hP, Matrix.trace_mul_comm, Matrix.mul_assoc, hOO, Matrix.trace_mul_comm]
  rw [hx, hy] at hq
  simpa [testingError, evaluate] using hq

open QAlgorithms.Papers.Independent.Claimed50.P15

theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (nu omega : Matrix I I ℂ) (hnu : nu.PosDef) (homega : omega.PosDef) :
    (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → optimalError false nu omega ≤ (petzOverlap nu omega s : EReal)) ∧
    (resolventOverlap nu omega : EReal) ≤ optimalError false nu omega := by
  obtain ⟨h1, h2⟩ := g58d_prop31 nu omega hnu homega
  constructor
  · intro s hs
    rw [h1, h2, EReal.coe_le_coe_iff]
    have := G59Q.audenaert omega nu homega hnu s hs
    unfold petzOverlap
    rw [G59Q.rpow_eq hnu.posSemidef.nonneg, G59Q.rpow_eq homega.posSemidef.nonneg,
      Matrix.trace_mul_comm]
    linarith
  · apply le_sInf
    rintro v ⟨T, hT, rfl⟩
    simp only [Bool.false_eq_true, if_false] at hT
    exact EReal.coe_le_coe_iff.mpr (g59_lower nu omega hnu homega T hT.1 hT.2)

end
