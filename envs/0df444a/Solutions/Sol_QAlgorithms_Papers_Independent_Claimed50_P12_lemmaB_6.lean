-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P12.lemmaB_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:29:53.807991+00:00
-- url     : https://prove2.me/submissions/c5bfdd9e-7ff3-4804-a0be-ae54b75ad5b5

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12
noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50
open QAlgorithms.Papers.Independent.Claimed50.P12
open scoped MatrixOrder

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

lemma g62j_trace_cfc_eq {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0) (htr : ∀ k : ℕ, (P ^ (k + 1)).trace = (Q ^ (k + 1)).trace) :
    (cfc f P).trace = (cfc f Q).trace := by
  classical
  set S : Finset ℝ := (P.finite_real_spectrum.union Q.finite_real_spectrum).toFinset ∪ {0} with hS
  set p : Polynomial ℝ := Lagrange.interpolate S id f with hp
  have hev : ∀ x ∈ S, p.eval x = f x := by
    intro x hx
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) f (Set.injOn_id _) hx
    exact this
  have hPe : cfc f P = Polynomial.aeval P p := by
    rw [← cfc_polynomial p P hP.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have hQe : cfc f Q = Polynomial.aeval Q p := by
    rw [← cfc_polynomial p Q hQ.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hev 0 (by simp [hS]), hf]
  rw [hPe, hQe, Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rcases i with _ | k
  · simp [h0]
  · rw [htr k]

lemma g62j_pow_succ_mul {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (k : ℕ) : (M * Mᴴ) ^ (k + 1) = M * (Mᴴ * M) ^ k * Mᴴ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

lemma g67r_sqrt_psd {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    (cfc Real.sqrt A).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun x _ => Real.sqrt_nonneg x)

lemma g67r_sqrt_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    cfc Real.sqrt A * cfc Real.sqrt A = A := by
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt A hA.nonneg]
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

lemma g67r_swap {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    (cfc Real.sqrt (A * Aᴴ)).trace = (cfc Real.sqrt (Aᴴ * A)).trace := by
  refine g62j_trace_cfc_eq _ _ (Matrix.isHermitian_mul_conjTranspose_self A)
    (Matrix.isHermitian_conjTranspose_mul_self A) _ Real.sqrt_zero fun k => ?_
  rw [g62j_pow_succ_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]

theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma W : Op I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef) :
    rootFidelity rho (W * sigma * Wᴴ) = rootFidelity (Wᴴ * rho * W) sigma := by
  set R := cfc Real.sqrt rho with hR
  set S := cfc Real.sqrt sigma with hS
  set T := cfc Real.sqrt (Wᴴ * rho * W) with hT
  have hRh : Rᴴ = R := (g67r_sqrt_psd rho).1
  have hSh : Sᴴ = S := (g67r_sqrt_psd sigma).1
  have hTh : Tᴴ = T := (g67r_sqrt_psd _).1
  have hRR : R * R = rho := g67r_sqrt_sq hrho
  have hSS : S * S = sigma := g67r_sqrt_sq hsigma
  have hpsd : (Wᴴ * rho * W).PosSemidef := by
    have := hrho.conjTranspose_mul_mul_same W
    simpa [Matrix.mul_assoc] using this
  have hTT : T * T = Wᴴ * rho * W := g67r_sqrt_sq hpsd
  set A := R * W * S with hA
  set B := S * T with hB
  have e1 : R * (W * sigma * Wᴴ) * R = A * Aᴴ := by
    rw [hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hRh, hSh, ← hSS]
    simp only [Matrix.mul_assoc]
  have e2 : Aᴴ * A = B * Bᴴ := by
    rw [hA, hB, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hRh, hSh,
      hTh]
    have : S * T * (T * S) = S * (T * T) * S := by simp only [Matrix.mul_assoc]
    rw [this, hTT, ← hRR]
    simp only [Matrix.mul_assoc]
  have e3 : Bᴴ * B = T * sigma * T := by
    rw [hB, Matrix.conjTranspose_mul, hSh, hTh, ← hSS]
    simp only [Matrix.mul_assoc]
  unfold rootFidelity
  rw [← hR, ← hT, e1, g67r_swap, e2, g67r_swap, e3]
