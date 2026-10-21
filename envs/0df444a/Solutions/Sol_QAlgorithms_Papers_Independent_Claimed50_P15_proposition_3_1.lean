-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P15.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T11:21:59.915995+00:00
-- url     : https://prove2.me/submissions/2a41547d-cfc1-4d8f-bba3-2ec05fbabeb2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15
noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction

open scoped MatrixOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15

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

theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
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
