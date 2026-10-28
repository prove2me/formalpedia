-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P29.smallSubspace_probability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T06:41:49.368004+00:00
-- url     : https://prove2.me/submissions/5e9b799f-1642-4962-9a9c-f3c55424b9ca

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29


noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

theorem X7T_proj {ι : Type*} [Fintype ι] [DecidableEq ι] (rho : Matrix ι ι ℂ)
    (hrho : rho.IsHermitian) (f : ℝ → ℝ) (hf : ∀ x, f x = 0 ∨ f x = 1) :
    let P := cfc f rho
    P * P = P ∧ Pᴴ = P ∧ P * rho = rho * P := by
  intro P
  have hsa : IsSelfAdjoint rho := hrho
  have hcont : ContinuousOn f (spectrum ℝ rho) := Matrix.finite_real_spectrum.continuousOn f
  refine ⟨?_, ?_, ?_⟩
  · show cfc f rho * cfc f rho = cfc f rho
    rw [← cfc_mul f f rho]
    congr 1
    funext x
    rcases hf x with h | h <;> simp [h]
  · exact (cfc_predicate f rho : IsSelfAdjoint (cfc f rho))
  · show cfc f rho * rho = rho * cfc f rho
    exact (Commute.refl rho).cfc_real f |>.symm.eq.symm

end QAlgorithms.Papers.Independent.Gap48.P29

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

theorem X7ss_dim {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℂ) (h : P * P = P) :
    P.trace = (projectionDimension P : ℂ) := by
  have he : IsIdempotentElem (Matrix.toEuclideanLin P) := by
    unfold IsIdempotentElem
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Module.End.mul_eq_comp, ← Matrix.toLin_mul, h]
  have := (LinearMap.IsIdempotentElem.isProj_range _ he).trace
  unfold projectionDimension
  rw [← this]
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun I ℂ).toBasis, LinearMap.toMatrix_toLin]

end QAlgorithms.Papers.Independent.Gap48.P29

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

theorem X7ss_re_nonneg {I : Type*} [Fintype I] (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    0 ≤ A.trace.re := by
  have := hA.trace_nonneg
  exact (Complex.nonneg_iff.mp this).1

theorem X7ss_proj_mul {I : Type*} [Fintype I] [DecidableEq I] (P A : Matrix I I ℂ)
    (hPh : Pᴴ = P) (hPP : P * P = P) (hA : A.PosSemidef) :
    0 ≤ (P * A).trace.re ∧ (P * A).trace.re ≤ A.trace.re := by
  have key : ∀ Q : Matrix I I ℂ, Qᴴ = Q → Q * Q = Q → (Q * A).trace = (Q * A * Qᴴ).trace := by
    intro Q h1 h2
    rw [h1, Matrix.trace_mul_comm (Q * A) Q, ← Matrix.mul_assoc, h2]
  constructor
  · rw [key P hPh hPP]; exact X7ss_re_nonneg _ (hA.mul_mul_conjTranspose_same P)
  · have h1 : (1 - P)ᴴ = 1 - P := by rw [Matrix.conjTranspose_sub, hPh, Matrix.conjTranspose_one]
    have h2 : (1 - P) * (1 - P) = 1 - P := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPP]; simp
    have := X7ss_re_nonneg _ (hA.mul_mul_conjTranspose_same (1 - P))
    rw [← key _ h1 h2, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at this
    linarith

open scoped MatrixOrder in
theorem X7ss_loewner {I : Type*} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ)
    (hrho : rho.IsHermitian) (f : ℝ → ℝ) (c : ℝ) (hf : ∀ x, f x * (c - x) ≥ 0) :
    (c • cfc f rho - cfc f rho * rho).PosSemidef := by
  have hsa : IsSelfAdjoint rho := hrho
  have e : c • cfc f rho - cfc f rho * rho = cfc (fun x => f x * (c - x)) rho := by
    have hc : ∀ g : ℝ → ℝ, ContinuousOn g (spectrum ℝ rho) := fun g =>
      Matrix.finite_real_spectrum.continuousOn g
    rw [cfc_mul f (fun x => c - x) rho (hc _) (hc _), cfc_sub (fun _ => c) (fun x => x) rho (hc _) (hc _), cfc_const c rho, cfc_id' ℝ rho,
      Matrix.mul_sub, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one]
  rw [e, ← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg fun x _ => hf x

end QAlgorithms.Papers.Independent.Gap48.P29

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

theorem X7ss_main (S : BlockQuantumSource) (hS : QAEP S)
    (window delta : ℝ) (hwindow : 0 < window) (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, ∀ P : Matrix (SourceRegister S.dimension n) (SourceRegister S.dimension n) ℂ,
      IsProjection P →
      (projectionDimension P : ℝ) <
        (1 - delta) * (2 : ℝ) ^ ((n : ℝ) * (sourceEntropyRate S - window)) →
      (P * S.rho n).trace.re ≤ delta := by
  set w := window / 2 with hw
  have hw0 : 0 < w := by positivity
  have hlim : Tendsto (fun n : ℕ => ((2 : ℝ) ^ (-w)) ^ n) atTop (nhds 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hev : ∀ᶠ n : ℕ in atTop, ((2 : ℝ) ^ (-w)) ^ n < delta / 2 :=
    hlim.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hS w hw0 (delta / 2) (by linarith), hev] with n hn hsmall
  intro P hP hdim
  set s := sourceEntropyRate S
  set rho := S.rho n with hrho_def
  have hrho := S.density n
  set f : ℝ → ℝ := fun x : ℝ => if (2 : ℝ) ^ (-(n : ℝ) * (s + w)) ≤ x ∧
      x ≤ (2 : ℝ) ^ (-(n : ℝ) * (s - w)) then 1 else 0 with hf
  set Pi := qaepSpectralProjector S w n with hPi
  have hPi' : Pi = cfc f rho := rfl
  obtain ⟨hPP, hPh, hPc⟩ := X7T_proj rho hrho.1.1 f (fun x => by
    simp only [hf]; split_ifs <;> simp)
  rw [← hPi'] at hPP hPh hPc
  set c : ℝ := (2 : ℝ) ^ (-(n : ℝ) * (s - w))
  have hc0 : 0 ≤ c := by positivity
  -- decomposition
  have hdec : rho = Pi * rho * Pi + (1 - Pi) * rho * (1 - Pi) := by
    have e1 : Pi * rho * Pi = Pi * rho := by rw [Matrix.mul_assoc, ← hPc, ← Matrix.mul_assoc, hPP]
    rw [e1, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, e1, ← hPc]
    abel
  have hPAP : (Pi * rho * Pi).PosSemidef := by
    have := hrho.1.mul_mul_conjTranspose_same Pi; rwa [hPh] at this
  have hQ : ((1 - Pi) * rho * (1 - Pi)).PosSemidef := by
    have := hrho.1.mul_mul_conjTranspose_same (1 - Pi)
    rwa [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh] at this
  have htr : (P * rho).trace.re = (P * (Pi * rho * Pi)).trace.re + (P * ((1 - Pi) * rho * (1 - Pi))).trace.re := by
    conv_lhs => rw [hdec]
    rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  -- second term
  have h2 : (P * ((1 - Pi) * rho * (1 - Pi))).trace.re < delta / 2 := by
    refine lt_of_le_of_lt (X7ss_proj_mul P _ hP.1 hP.2 hQ).2 ?_
    have h1 : ((1 - Pi) * rho * (1 - Pi)).trace.re = 1 - qaepRetainedMass S w n := by
      have := congrArg (fun M => M.trace.re) hdec
      simp only [Matrix.trace_add, Complex.add_re] at this
      have ht : rho.trace.re = 1 := by rw [hrho.2]; simp
      unfold qaepRetainedMass
      rw [← hPi, ← hrho_def]
      linarith
    rw [h1]; linarith
  -- first term
  have hL : (c • Pi - Pi * rho * Pi).PosSemidef := by
    have e1 : Pi * rho * Pi = Pi * rho := by rw [Matrix.mul_assoc, ← hPc, ← Matrix.mul_assoc, hPP]
    rw [e1, hPi']
    refine X7ss_loewner rho hrho.1.1 f c fun x => ?_
    simp only [hf]; split_ifs with h
    · simp only [one_mul]; linarith [h.2]
    · simp
  have hPpsd : P.PosSemidef := by
    have := Matrix.posSemidef_self_mul_conjTranspose P
    rwa [hP.1.eq, hP.2] at this
  have h1a : (P * (Pi * rho * Pi)).trace.re ≤ c * (P * Pi).trace.re := by
    have := (X7ss_proj_mul P _ hP.1 hP.2 hL).1
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, Matrix.mul_smul, Matrix.trace_smul] at this
    simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] at this
    linarith
  have h1b : (P * Pi).trace.re ≤ (projectionDimension P : ℝ) := by
    rw [Matrix.trace_mul_comm]
    refine le_trans (X7ss_proj_mul Pi P hPh hPP hPpsd).2 (le_of_eq ?_)
    rw [X7ss_dim P hP.2]; simp
  have hX : c * (2 : ℝ) ^ ((n : ℝ) * (s - window)) = ((2 : ℝ) ^ (-w)) ^ n := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1; rw [hw]; ring
  have hpos : 0 < (2 : ℝ) ^ ((n : ℝ) * (s - window)) := by positivity
  have h1 : (P * (Pi * rho * Pi)).trace.re < delta / 2 := by
    have : c * (projectionDimension P : ℝ) ≤ c * (2 : ℝ) ^ ((n : ℝ) * (s - window)) := by
      apply mul_le_mul_of_nonneg_left _ hc0
      nlinarith
    nlinarith
  linarith

end QAlgorithms.Papers.Independent.Gap48.P29

end

open QAlgorithms.Papers.Independent.Gap48.P29 QAlgorithms Filter in
open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection) in
theorem solution (S : BlockQuantumSource) (hS : QAEP S)
    (window delta : ℝ) (hwindow : 0 < window) (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, ∀ P : Matrix (SourceRegister S.dimension n) (SourceRegister S.dimension n) ℂ,
      IsProjection P →
      (projectionDimension P : ℝ) <
        (1 - delta) * (2 : ℝ) ^ ((n : ℝ) * (sourceEntropyRate S - window)) →
      (P * S.rho n).trace.re ≤ delta :=
  X7ss_main S hS window delta hwindow hdelta
