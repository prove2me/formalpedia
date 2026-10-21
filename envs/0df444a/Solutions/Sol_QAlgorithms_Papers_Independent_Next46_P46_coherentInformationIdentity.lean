-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P46.coherentInformationIdentity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:22:26.992564+00:00
-- url     : https://prove2.me/submissions/d56521a6-d00f-4b34-9ffa-2e596f761179

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P46
noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Next46 QAlgorithms.Papers.Independent.Next46.P46

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.decEq Classical.propDecidable

-- The repair request explicitly authorizes imports from the pinned accepted papers.

open QAlgorithms.Papers.Independent.Information100.P21 (Vec Op)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Frontier30.P12
  (coherentInfo quantumMutualInfo mutualAE marginalAE triCopies EntProtocol RectangularKrausData)

open QAlgorithms.Papers.Independent.Dependency50.P19 (channelSource)

open QAlgorithms.Papers.Independent.Dependency50.P48 (IsDilation)

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

lemma g62j_trace_pow {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (k : ℕ) :
    ((M * Mᴴ) ^ (k + 1)).trace = ((Mᵀ * (Mᵀ)ᴴ) ^ (k + 1)).trace := by
  have h1 : Mᵀ * (Mᵀ)ᴴ = (Mᴴ * M)ᵀ := by
    rw [Matrix.transpose_mul]; rfl
  rw [h1, ← Matrix.transpose_pow, Matrix.trace_transpose, g62j_pow_succ_mul, Matrix.mul_assoc,
    Matrix.trace_mul_comm, pow_succ, Matrix.mul_assoc]

lemma g62j_entropy_swap {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) : vnEntropy (M * Mᴴ) = vnEntropy (Mᵀ * (Mᵀ)ᴴ) := by
  unfold vnEntropy
  rw [g62j_trace_cfc_eq _ _ (Matrix.isHermitian_mul_conjTranspose_self M)
    (Matrix.isHermitian_mul_conjTranspose_self Mᵀ) _ (by simp) (g62j_trace_pow M)]

/-- arXiv:quant-ph/0307053v1, PDF p.2: coherent and dephased entropies.
The conditional BE vectors are orthonormal, and zero Schmidt weights are allowed.
Purity and the entropy identity are conclusions of the source model, not assumptions. -/
theorem solution {X B E : Type} [Fintype X] [Fintype B] [Fintype E]
    [Nonempty X] [Nonempty B] [Nonempty E]
    (p : X → ℝ) (hp : IsLaw p) (phi : X → Vec (B × E))
    (hphi : Orthonormal ℂ phi) :
    let psi := WithLp.toLp 2 (fun z : X × (B × E) => (Real.sqrt (p z.1) : ℂ) * phi z.1 z.2)
    let rho := pureDensity psi
    let barRho := dephased p phi
    coherentInfo (marginalAB rho) =
      vnEntropy (traceRight (traceLeft rho)) - vnEntropy (traceLeft (traceLeft rho)) ∧
    vnEntropy (traceRight (traceLeft rho)) - vnEntropy (traceLeft (traceLeft rho)) =
      quantumMutualInfo (marginalAB barRho) - quantumMutualInfo (marginalAE barRho) := by
  intro psi rho barRho
  have hpsi : ∀ z : X × (B × E), psi z = (Real.sqrt (p z.1) : ℂ) * phi z.1 z.2 := fun z => rfl
  have hsq : ∀ x, (Real.sqrt (p x) : ℂ) * (Real.sqrt (p x) : ℂ) = (p x : ℂ) := by
    intro x; rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hp.1 x)]
  -- marginals of rho
  have eXB : marginalAB rho = (Matrix.of fun (xb : X × B) (e : E) => psi (xb.1, (xb.2, e))) *
      (Matrix.of fun (xb : X × B) (e : E) => psi (xb.1, (xb.2, e)))ᴴ := by
    ext i j; simp [marginalAB, rho, pureDensity, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have eE : traceLeft (traceLeft rho) =
      (Matrix.of fun (xb : X × B) (e : E) => psi (xb.1, (xb.2, e)))ᵀ *
      ((Matrix.of fun (xb : X × B) (e : E) => psi (xb.1, (xb.2, e)))ᵀ)ᴴ := by
    ext i j; simp [traceLeft, rho, pureDensity, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type]
    exact Finset.sum_comm
  have eB : traceLeft (marginalAB rho) = traceRight (traceLeft rho) := by
    ext i j; simp [traceLeft, traceRight, marginalAB]
    exact Finset.sum_comm
  refine ⟨?_, ?_⟩
  · rw [coherentInfo, eB, eXB, eE, ← g62j_entropy_swap]
  · -- dephased marginals
    set M : Matrix (X × B) (X × E) ℂ := Matrix.of fun xb xe =>
      if xb.1 = xe.1 then (Real.sqrt (p xb.1) : ℂ) * phi xb.1 (xb.2, xe.2) else 0 with hM
    have fXB : marginalAB barRho = M * Mᴴ := by
      ext i j
      simp only [marginalAB, barRho, dephased, pureDensity, Matrix.mul_apply,
        Matrix.conjTranspose_apply, hM, Matrix.of_apply, Fintype.sum_prod_type]
      by_cases h : i.1 = j.1
      · rw [Finset.sum_eq_single j.1]
        · simp only [h, if_true]
          refine Finset.sum_congr rfl (fun e _ => ?_)
          simp only [RCLike.star_def, map_mul, Complex.conj_ofReal]
          rw [← hsq]; ring
        · intro b _ hb; simp [hb, Ne.symm hb]
        · simp
      · simp only [h, if_false, Finset.sum_const_zero]
        symm
        apply Finset.sum_eq_zero
        intro x _
        apply Finset.sum_eq_zero
        intro e _
        by_cases h1 : i.1 = x
        · have h2 : ¬ j.1 = x := fun h2 => h (h1.trans h2.symm)
          simp [h2]
        · simp [h1]
    have fXE : marginalAE barRho = Mᵀ * (Mᵀ)ᴴ := by
      ext i j
      simp only [marginalAE, barRho, dephased, pureDensity, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.transpose_apply, hM, Matrix.of_apply,
        Fintype.sum_prod_type]
      by_cases h : i.1 = j.1
      · rw [Finset.sum_eq_single j.1]
        · simp only [h, if_true]
          refine Finset.sum_congr rfl (fun e _ => ?_)
          simp only [RCLike.star_def, map_mul, Complex.conj_ofReal]
          rw [← hsq]; ring
        · intro b _ hb; simp [hb, Ne.symm hb]
        · simp
      · simp only [h, if_false, Finset.sum_const_zero]
        symm
        apply Finset.sum_eq_zero
        intro x _
        apply Finset.sum_eq_zero
        intro e _
        by_cases h1 : x = i.1
        · have h2 : ¬ x = j.1 := fun h2 => h (h1.symm.trans h2)
          simp [h2]
        · simp [h1]
    have fX : traceRight (marginalAE barRho) = traceRight (marginalAB barRho) := by
      ext i j; simp only [traceRight, marginalAE, marginalAB, Matrix.of_apply]
      exact Finset.sum_comm
    have fB : traceLeft (marginalAB barRho) = traceRight (traceLeft rho) := by
      ext i j
      simp only [traceLeft, traceRight, marginalAB, barRho, dephased, rho, pureDensity,
        Matrix.of_apply, hpsi, if_true]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun x _ => ?_))
      simp only [map_mul, Complex.conj_ofReal]
      rw [← hsq]; ring
    have fE : traceLeft (marginalAE barRho) = traceLeft (traceLeft rho) := by
      ext i j
      simp only [traceLeft, marginalAE, barRho, dephased, rho, pureDensity,
        Matrix.of_apply, hpsi, if_true]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun x _ => ?_))
      simp only [map_mul, Complex.conj_ofReal]
      rw [← hsq]; ring
    have hS : vnEntropy (marginalAB barRho) = vnEntropy (marginalAE barRho) := by
      rw [fXB, fXE, g62j_entropy_swap]
    simp only [quantumMutualInfo]
    rw [fX, fB, fE, hS]
    ring



end
