-- Prove2me | solution 1 for QAlgorithms.Nannicini.phaseEstimation_inexactEigenstate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:44:27.536568+00:00
-- url     : https://prove2.me/submissions/b7d928c1-7bef-41e7-92fd-b4b77b7eb388

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
set_option autoImplicit false

open QAlgorithms
open scoped ComplexConjugate

private lemma ip_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) : act (A * B) x = act A (act B x) := by
  simp only [act, Matrix.mulVec_mulVec, WithLp.ofLp_toLp]

private lemma ip_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (c : ℂ) (x : EuclideanSpace ℂ ι) : act A (c • x) = c • act A x := by
  ext i
  simp [act, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]

private lemma ip_adjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    inner ℂ x (act A y) = inner ℂ (act (star A) x) y := by
  change inner ℂ x (Matrix.toEuclideanLin A y) =
    inner ℂ (Matrix.toEuclideanLin (star A) x) y
  rw [Matrix.star_eq_conjTranspose, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact (LinearMap.adjoint_inner_left _ _ _).symm

private lemma ip_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) (c : ℂ)
    (hc : act U v = c • v) (r : ℕ) : act (U ^ r) v = c ^ r • v := by
  induction r with
  | zero => ext i; simp [act]
  | succ r ih => rw [pow_succ', ip_mul, ih, ip_smul, hc, smul_smul, pow_succ]

private lemma ip_slice {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (U : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) (a : Qubits m) :
    (WithLp.toLp 2 (fun b => phaseEstimationState m U x (a,b)) : EuclideanSpace ℂ ι) =
      ∑ k : Qubits m, ((star (qftQubits m) a k) *
        (act (qftQubits m) (zeroKet m) k)) • act (U ^ bitsToNat k) x := by
  have ht (A : Matrix (Qubits m) (Qubits m) ℂ) (v : EuclideanSpace ℂ (Qubits m)) :
      act (Matrix.kronecker A (1 : Matrix ι ι ℂ)) (tensorVec v x) =
        tensorVec (act A v) x := by
    ext ⟨i,j⟩
    simp [act, tensorVec, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.one_apply, Finset.sum_mul, mul_assoc]
  have hf (A : Matrix (Qubits m) (Qubits m) ℂ)
      (w : EuclideanSpace ℂ (Qubits m × ι)) (i : Qubits m) (j : ι) :
      act (Matrix.kronecker A (1 : Matrix ι ι ℂ)) w (i,j) =
        ∑ k, A i k * w (k,j) := by
    simp [act, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]
  have hp (v : EuclideanSpace ℂ (Qubits m)) (i : Qubits m) (j : ι) :
      act (controlledPower m U) (tensorVec v x) (i,j) =
        v i * act (U ^ bitsToNat i) x j := by
    simp [act, controlledPower, tensorVec, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Finset.mul_sum, mul_left_comm]
  ext b
  change phaseEstimationState m U x (a,b) = _
  unfold phaseEstimationState
  rw [ip_mul, ip_mul, ht, hf]
  simp_rw [hp]
  simp [mul_assoc]

private lemma ip_slice_eigen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (U : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) (c : ℂ)
    (hc : act U v = c • v) (a : Qubits m) :
    (WithLp.toLp 2 (fun b => phaseEstimationState m U v (a,b)) : EuclideanSpace ℂ ι) =
      (∑ k : Qubits m, (star (qftQubits m) a k) *
        (act (qftQubits m) (zeroKet m) k) * c ^ bitsToNat k) • v := by
  rw [ip_slice]
  simp_rw [ip_pow U v c hc, smul_smul]
  rw [Finset.sum_smul]

private lemma ip_slice_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (v x : EuclideanSpace ℂ ι) (c : ℂ) (hc : act U v = c • v)
    (hcunit : star c * c = 1) (a : Qubits m) :
    inner ℂ v (WithLp.toLp 2 (fun b => phaseEstimationState m U x (a,b))) =
      (∑ k : Qubits m, (star (qftQubits m) a k) *
        (act (qftQubits m) (zeroKet m) k) * c ^ bitsToNat k) * inner ℂ v x := by
  have hadj : act (star U) v = star c • v := by
    have h := congrArg (act (star U)) hc
    rw [← ip_mul, Unitary.star_mul_self_of_mem hU, ip_smul] at h
    simp only [act, Matrix.one_mulVec, WithLp.toLp_ofLp] at h
    change v = c • act (star U) v at h
    calc
      act (star U) v = (star c * c) • act (star U) v := by rw [hcunit, one_smul]
      _ = star c • v := by rw [mul_smul, ← h]
  have hpow (r : ℕ) : inner ℂ v (act (U ^ r) x) = c ^ r * inner ℂ v x := by
    rw [ip_adjoint, star_pow, ip_pow (star U) v (star c) hadj]
    simp [mul_comm]
  rw [ip_slice, inner_sum]
  simp_rw [inner_smul_right, hpow]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

private lemma ip_event_slices {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (x : EuclideanSpace ℂ (ι × κ))
    (P : ι → Prop) [DecidablePred P] :
    probEvent x (fun z => P z.1) =
      ∑ a ∈ Finset.univ.filter P,
        ‖(WithLp.toLp 2 (fun b => x (a,b)) : EuclideanSpace ℂ κ)‖ ^ 2 := by
  classical
  simp only [probEvent, Finset.sum_filter, prob, ket, EuclideanSpace.inner_single_left]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : P a
  · simp only [h, ite_true]
    simpa using (EuclideanSpace.norm_sq_eq
      (WithLp.toLp 2 (fun b => x (a,b)) : EuclideanSpace ℂ κ)).symm
  · simp [h]

private lemma ip_domination {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (v x : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) (c : ℂ)
    (hc : act U v = c • v) (hcunit : star c * c = 1)
    (P : Qubits m → Prop) [DecidablePred P] :
    probEvent (phaseEstimationState m U v) (fun z => P z.1) * ‖inner ℂ v x‖ ^ 2 ≤
      probEvent (phaseEstimationState m U x) (fun z => P z.1) := by
  classical
  rw [ip_event_slices, ip_event_slices, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  rw [ip_slice_eigen m U v c hc, norm_smul, hv, mul_one]
  have h := norm_inner_le_norm (𝕜 := ℂ) v
    (WithLp.toLp 2 (fun b => phaseEstimationState m U x (a,b)))
  rw [hv, one_mul, ip_slice_inner m U hU v x c hc hcunit, norm_mul] at h
  simpa only [mul_pow] using pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h 2

theorem solution (n m : ℕ) (U : Matrix (Qubits n) (Qubits n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (ε δ : ℝ) (hε : 0 < ε) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1)
    (hQPE : ∀ (v : EuclideanSpace ℂ (Qubits n)) (φ : ℝ), IsState v → 0 ≤ φ → φ < 1 →
      act U v = Complex.exp (2 * Real.pi * Complex.I * (φ : ℂ)) • v →
      probEvent (phaseEstimationState m U v)
        (fun z => circDist ((bitsToNat z.1 : ℝ) / (2 : ℝ) ^ m) φ < ε) ≥ 1 - δ)
    (psiStar : EuclideanSpace ℂ (Qubits n)) (phiStar : ℝ) (hpsi : IsState psiStar)
    (hphi0 : 0 ≤ phiStar) (hphi1 : phiStar < 1)
    (heig : act U psiStar = Complex.exp (2 * Real.pi * Complex.I * (phiStar : ℂ)) • psiStar)
    (xi : EuclideanSpace ℂ (Qubits n)) (hxi : IsState xi) :
    probEvent (phaseEstimationState m U xi)
        (fun z => circDist ((bitsToNat z.1 : ℝ) / (2 : ℝ) ^ m) phiStar < ε) ≥
      (1 - δ) * ‖inner ℂ xi psiStar‖ ^ 2 := by
  classical
  have hcunit : star (Complex.exp (2 * Real.pi * Complex.I * (phiStar : ℂ))) *
      Complex.exp (2 * Real.pi * Complex.I * (phiStar : ℂ)) = 1 := by
    simp only [Complex.star_def, ← Complex.exp_conj, map_mul, map_ofNat,
      Complex.conj_ofReal, Complex.conj_I]
    rw [← Complex.exp_add]
    have hz : 2 * (Real.pi : ℂ) * -Complex.I * (phiStar : ℂ) +
        2 * (Real.pi : ℂ) * Complex.I * (phiStar : ℂ) = 0 := by ring
    rw [hz, Complex.exp_zero]
  have hdom := ip_domination m U hU psiStar xi hpsi _ heig hcunit
    (fun a => circDist ((bitsToNat a : ℝ) / (2 : ℝ) ^ m) phiStar < ε)
  have hbase := hQPE psiStar phiStar hpsi hphi0 hphi1 heig
  have hov : ‖inner ℂ xi psiStar‖ = ‖inner ℂ psiStar xi‖ := norm_inner_symm _ _
  rw [hov]
  exact (mul_le_mul_of_nonneg_right hbase (sq_nonneg _)).trans hdom
