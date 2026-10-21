-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P23.quantum_entropy_balance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:27:23.451481+00:00
-- url     : https://prove2.me/submissions/4ccd0c18-5a7e-49a0-848a-b9616cf21ad8

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23
noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

open QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem g64d_scalar_klein {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 < p i) (w : ι → ι → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j = 1) (hcol : ∀ j, ∑ i, w i j = 1) :
    ∑ i, ∑ j, w i j * (p j * Real.log (p i)) ≤ ∑ i, p i * Real.log (p i) := by
  have h1 : ∀ i j, w i j * (p j * Real.log (p i)) ≤
      w i j * (p j * Real.log (p j)) + w i j * p i - w i j * p j := by
    intro i j
    have hq := Real.log_le_sub_one_of_pos (div_pos (hp i) (hp j))
    rw [Real.log_div (hp i).ne' (hp j).ne'] at hq
    have : p j * Real.log (p i) ≤ p j * Real.log (p j) + p i - p j := by
      have := mul_le_mul_of_nonneg_left hq (hp j).le
      rw [mul_sub, mul_sub, mul_div_cancel₀ _ (hp j).ne', mul_one] at this
      linarith
    nlinarith [hw i j]
  calc ∑ i, ∑ j, w i j * (p j * Real.log (p i))
      ≤ ∑ i, ∑ j, (w i j * (p j * Real.log (p j)) + w i j * p i - w i j * p j) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
    _ = ∑ j, p j * Real.log (p j) + ∑ i, p i - ∑ j, p j := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i j => w i j * (p j * Real.log (p j))),
          Finset.sum_comm (f := fun i j => w i j * p j)]
        simp only [← Finset.sum_mul, hcol, ← Finset.mul_sum, hrow, one_mul, mul_one]
    _ = ∑ i, p i * Real.log (p i) := by ring

theorem g64d_klein (ω : Mat I) (hω : ω.PosDef) (V : Mat I) (hV1 : V * Vᴴ = 1) (hV2 : Vᴴ * V = 1) :
    (cfc Real.log ω * (V * ω * Vᴴ)).trace.re ≤ (cfc Real.log ω * ω).trace.re := by
  set hA := hω.1 with hhA
  set W : Mat I := (hA.eigenvectorUnitary : Mat I) with hW
  have hW1 : W * Wᴴ = 1 := by
    rw [hW, ← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem (SetLike.coe_mem _)
  have hW2 : Wᴴ * W = 1 := by
    rw [hW, ← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem (SetLike.coe_mem _)
  set p := hA.eigenvalues with hp
  have hpos : ∀ i, 0 < p i := fun i => hω.eigenvalues_pos i
  have hωe : ω = W * Matrix.diagonal (fun i => (p i : ℂ)) * Wᴴ := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [hW, Matrix.star_eq_conjTranspose, Function.comp_def, hp]
  have hLe : cfc Real.log ω = W * Matrix.diagonal (fun i => (Real.log (p i) : ℂ)) * Wᴴ := by
    rw [hA.cfc_eq, Matrix.IsHermitian.cfc]
    simp [hW, Matrix.star_eq_conjTranspose, Function.comp_def, hp]
  set M := Wᴴ * V * W with hM
  have hM1 : M * Mᴴ = 1 := by
    rw [hM]; simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc W Wᴴ, hW1, Matrix.one_mul, ← Matrix.mul_assoc V Vᴴ, hV1, Matrix.one_mul, hW2]
  have hM2 : Mᴴ * M = 1 := by
    rw [hM]; simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc W Wᴴ, hW1, Matrix.one_mul, ← Matrix.mul_assoc Vᴴ V, hV2, Matrix.one_mul, hW2]
  set Λ := Matrix.diagonal (fun i => (Real.log (p i) : ℂ))
  set D := Matrix.diagonal (fun i => (p i : ℂ))
  have trW : ∀ X : Mat I, (W * X * Wᴴ).trace = X.trace := by
    intro X; rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hW2, Matrix.one_mul]
  have e1 : (cfc Real.log ω * (V * ω * Vᴴ)).trace = (Λ * M * D * Mᴴ).trace := by
    have hx : W * Λ * Wᴴ * (V * (W * D * Wᴴ) * Vᴴ) = W * (Λ * M * D * Mᴴ) * Wᴴ := by
      rw [hM]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [hW1, Matrix.mul_one]
    rw [hLe, hωe, hx, trW]
  have e2 : (cfc Real.log ω * ω).trace = (Λ * D).trace := by
    have hx : W * Λ * Wᴴ * (W * D * Wᴴ) = W * (Λ * D) * Wᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Wᴴ W, hW2, Matrix.one_mul]
    rw [hLe, hωe, hx, trW]
  have hterm : ∀ i k, Real.log (p i) * M i k * p k * star (M i k) =
      ((Complex.normSq (M i k) * (p k * Real.log (p i)) : ℝ) : ℂ) := by
    intro i k
    rw [show Real.log (p i) * M i k * p k * star (M i k) =
      (Real.log (p i) * p k : ℂ) * (M i k * (starRingEnd ℂ) (M i k)) by
        simp only [RCLike.star_def]; ring, Complex.mul_conj]
    push_cast; ring
  have e3 : (Λ * M * D * Mᴴ).trace.re = ∑ i, ∑ k, Complex.normSq (M i k) * (p k * Real.log (p i)) := by
    simp only [Matrix.trace, Matrix.diag]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, hterm, Complex.ofReal_re]
  have e4 : (Λ * D).trace.re = ∑ i, p i * Real.log (p i) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Λ, D]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.ofReal_mul, Complex.ofReal_re, mul_comm]
  have hrow : ∀ i, ∑ k, Complex.normSq (M i k) = 1 := by
    intro i
    have := congrFun (congrFun hM1 i) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at this
    have h2 : ∑ k, M i k * star (M i k) = ((∑ k, Complex.normSq (M i k) : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [RCLike.star_def, Complex.mul_conj]
    rw [h2] at this
    exact_mod_cast this
  have hcol : ∀ k, ∑ i, Complex.normSq (M i k) = 1 := by
    intro k
    have := congrFun (congrFun hM2 k) k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at this
    have h2 : ∑ i, star (M i k) * M i k = ((∑ i, Complex.normSq (M i k) : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm, RCLike.star_def, Complex.mul_conj]
    rw [h2] at this
    exact_mod_cast this
  rw [e1, e2, e3, e4]
  exact g64d_scalar_klein p hpos _ (fun i k => Complex.normSq_nonneg _) hrow hcol
theorem g64d_conj_deriv (K B : Mat I) (s : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • K) * B * NormedSpace.exp ((s : ℂ) • (-K)))
      (NormedSpace.exp ((s : ℂ) • K) * K * B * NormedSpace.exp ((s : ℂ) • (-K)) +
        NormedSpace.exp ((s : ℂ) • K) * B * (NormedSpace.exp ((s : ℂ) • (-K)) * (-K))) s := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℂ) K (s : ℂ)
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℂ) (-K) (s : ℂ)
  have h3 := ((h1.mul_const B).mul h2).scomp (h := ⇑Complex.ofRealCLM) s Complex.ofRealCLM.hasDerivAt
  have e : ((fun y : ℂ => NormedSpace.exp (y • K) * B) * fun u : ℂ => NormedSpace.exp (u • -K)) ∘
      ⇑Complex.ofRealCLM = fun s : ℝ => NormedSpace.exp ((s : ℂ) • K) * B *
        NormedSpace.exp ((s : ℂ) • (-K)) := by
    funext t; rfl
  rw [e, Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul] at h3
  exact h3

theorem g64d_conj_cont (K B : Mat I) :
    Continuous (fun s : ℝ => NormedSpace.exp ((s : ℂ) • K) * B * NormedSpace.exp ((s : ℂ) • (-K))) :=
  continuous_iff_continuousAt.2 fun s => (g64d_conj_deriv K B s).continuousAt

noncomputable def g64d_trR (L : Mat I) : Mat I →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => (X * L).trace.re
      map_add' := fun X Y => by simp [Matrix.add_mul, Matrix.trace_add]
      map_smul' := fun c X => by simp [Matrix.smul_mul, Matrix.trace_smul] }

theorem g64d_trR_apply (L X : Mat I) : g64d_trR L X = (X * L).trace.re := rfl

lemma g64d_padd (H : Mat I) (t s : ℝ) :
    propagator H t * propagator H s = propagator H (t+s) := by
  unfold propagator
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl H).smul_left _).smul_right _), ← add_smul]
  congr 2
  push_cast; ring

lemma g64d_p0 (H : Mat I) : propagator H 0 = 1 := by simp [propagator]

lemma g64d_pstar (H : Mat I) (hH : H.IsHermitian) (t : ℝ) :
    (propagator H t)ᴴ = propagator H (-t) := by
  unfold propagator
  rw [← Matrix.star_eq_conjTranspose, NormedSpace.star_exp, star_smul, Matrix.star_eq_conjTranspose, hH.eq]
  congr 2
  simp

def g64d_conjHom (U : Mat I) (h1 : U * Uᴴ = 1) (h2 : Uᴴ * U = 1) : Mat I →⋆ₐ[ℝ] Mat I where
  toFun X := U * X * Uᴴ
  map_one' := by simp [h1]
  map_mul' X Y := by
    show U * (X * Y) * Uᴴ = (U * X * Uᴴ) * (U * Y * Uᴴ)
    calc U * (X * Y) * Uᴴ = U * X * (Uᴴ * U) * Y * Uᴴ := by rw [h2]; simp [Matrix.mul_assoc]
      _ = _ := by simp [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one, h1]
  map_star' X := by simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma g64d_cfctau (f : ℝ → ℝ) (H : Mat I) (hH : H.IsHermitian) (s : ℝ) (ω : Mat I) (hω : ω.IsHermitian) :
    cfc f (tau H s ω) = tau H s (cfc f ω) := by
  have hs : (propagator H (-s))ᴴ = propagator H s := by rw [g64d_pstar H hH, neg_neg]
  have h1 : propagator H (-s) * (propagator H (-s))ᴴ = 1 := by rw [hs, g64d_padd]; simp [g64d_p0]
  have h2 : (propagator H (-s))ᴴ * propagator H (-s) = 1 := by rw [hs, g64d_padd]; simp [g64d_p0]
  have := StarAlgHom.map_cfc (g64d_conjHom _ h1 h2) f ω ((Matrix.finite_real_spectrum).continuousOn _)
    (by show Continuous fun X => propagator H (-s) * X * (propagator H (-s))ᴴ; fun_prop)
    hω.isSelfAdjoint (hω.isSelfAdjoint.map _)
  have e : ∀ X, (g64d_conjHom _ h1 h2) X = tau H s X := by
    intro X; show _ * X * _ = _; rw [hs]; rfl
  rw [e, e] at this
  exact this.symm

lemma g64d_tr_tau (H : Mat I) (s : ℝ) (X : Mat I) : (tau H s X).trace = X.trace := by
  unfold tau
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, g64d_padd]; simp [g64d_p0]

lemma g64d_tau_exp (H B : Mat I) (t : ℝ) : tau H t B =
    NormedSpace.exp ((t : ℂ) • (-(-(Complex.I • H)))) * B *
      NormedSpace.exp ((t : ℂ) • (-(Complex.I • H))) := by
  unfold tau propagator
  rw [neg_neg]
  congr 2
  · rw [smul_smul]; push_cast; ring_nf
  · rw [smul_neg, smul_smul, ← neg_smul]; congr 1; ring

lemma g64d_evolved_exp (H B : Mat I) (t : ℝ) : evolved H B t =
    NormedSpace.exp ((t : ℂ) • (-(Complex.I • H))) * B *
      NormedSpace.exp ((t : ℂ) • (-(-(Complex.I • H)))) := by
  unfold evolved tau propagator
  rw [neg_neg]
  congr 2
  · simp only [neg_neg, smul_neg, smul_smul, ← neg_smul]; congr 1; push_cast; ring
  · simp only [neg_neg, smul_smul]; push_cast; ring_nf

lemma g64d_alg (E F K L w : Mat I) (hEK : E * K = K * E) :
    ((E * K * w * F + E * w * (F * (-K))) * L).trace = -((F * (K * L - L * K) * E) * w).trace := by
  have a1 : (E * w * (F * (-K)) * L).trace = -(F * (K * L) * E * w).trace := by
    rw [show E * w * (F * (-K)) * L = -((E * w) * (F * K * L)) by noncomm_ring,
      Matrix.trace_neg, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have a2 : (E * K * w * F * L).trace = (F * (L * K) * E * w).trace := by
    rw [hEK, show K * E * w * F * L = K * (E * w * F * L) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, show E * w * F * L * K = (E * w) * (F * L * K) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [Matrix.add_mul, Matrix.trace_add, a1, a2, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul,
    Matrix.trace_sub]
  ring

theorem solution [Nonempty I] (H omega : Mat I) (hH : H.IsHermitian)
    (homega : QAlgorithms.IsDensityMatrix omega) (hfaithful : omega.PosDef) :
    (∀ t : ℝ, signedRelativeEntropy (evolved H omega t) omega =
      ((-(∫ s in (0 : ℝ)..t, ev omega (tau H s (entropyProduction H omega))) : ℝ) : EReal)) ∧
    (∀ t : ℝ, 0 < t → ev omega (averagedProduction H omega t) =
      t⁻¹ * ∫ s in (0 : ℝ)..t, ev omega (tau H s (entropyProduction H omega)) ∧
        0 ≤ ev omega (averagedProduction H omega t)) := by
  have hω : omega.IsHermitian := hfaithful.1
  set K : Mat I := -(Complex.I • H) with hK
  set L : Mat I := logMat omega with hL
  set σ := entropyProduction H omega with hσ
  have hσK : σ = K * L - L * K := by
    rw [hσ, entropyProduction, hK, ← hL]
    simp only [neg_smul, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  -- F(s) = re tr(ω_s L)
  set F : ℝ → ℝ := fun s => g64d_trR L (evolved H omega s) with hF
  have hev : ∀ X, ev omega X = g64d_trR omega X := fun X => rfl
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s => -F s) (ev omega (tau H s σ)) s := by
    intro s
    have h0 := g64d_conj_deriv K omega s
    have h1 := (g64d_trR L).hasFDerivAt.comp_hasDerivAt s h0
    have h2 := h1.neg
    have e1 : (fun s => -F s) = fun s => -((g64d_trR L) ∘ (fun s : ℝ =>
        NormedSpace.exp ((s : ℂ) • K) * omega * NormedSpace.exp ((s : ℂ) • (-K)))) s := by
      funext s; simp only [hF, Function.comp, g64d_evolved_exp, hK]
    rw [e1]
    refine h2.congr_deriv ?_
    have hEK : NormedSpace.exp ((s : ℂ) • K) * K = K * NormedSpace.exp ((s : ℂ) • K) :=
      (((Commute.refl K).smul_left (s : ℂ)).exp_left).eq
    rw [g64d_trR_apply, g64d_alg _ _ _ _ _ hEK, Complex.neg_re, neg_neg, hev, g64d_trR_apply,
      g64d_tau_exp, hσK, hK]
  have hcont : Continuous fun s => ev omega (tau H s σ) := by
    have e : (fun s => ev omega (tau H s σ)) = (g64d_trR omega) ∘ (fun s : ℝ =>
        NormedSpace.exp ((s : ℂ) • (-K)) * σ * NormedSpace.exp ((s : ℂ) • (-(-K)))) := by
      funext s; simp only [Function.comp, hev, g64d_tau_exp, hK, neg_neg]
    rw [e]; exact (g64d_trR omega).continuous.comp (g64d_conj_cont (-K) σ)
  have hFTC : ∀ t, ∫ s in (0 : ℝ)..t, ev omega (tau H s σ) = F 0 - F t := by
    intro t
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
      (hcont.intervalIntegrable _ _)]
    ring
  have hF0 : F 0 = (omega * L).trace.re := by
    simp only [hF, g64d_trR_apply, evolved, show -(0:ℝ) = 0 by simp]
    simp [tau, g64d_p0]
  -- relative entropy
  have hrel : ∀ t, signedRelativeEntropy (evolved H omega t) omega = ((F t - F 0 : ℝ) : EReal) := by
    intro t
    have hsupp : QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported (evolved H omega t) omega := by
      intro v hv
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
      have : v = 0 := by
        by_contra hne
        have := hfaithful.dotProduct_mulVec_pos hne
        rw [hv] at this; simp at this
      rw [this, Matrix.mulVec_zero]
    unfold signedRelativeEntropy QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy
    rw [if_pos hsupp]
    have hf : (cfc (fun x : ℝ => x * Real.log x) (evolved H omega t)).trace = (omega * L).trace := by
      rw [evolved, g64d_cfctau _ H hH _ omega hω, g64d_tr_tau,
        cfc_mul (fun x : ℝ => x) Real.log omega ((Matrix.finite_real_spectrum).continuousOn _)
          ((Matrix.finite_real_spectrum).continuousOn _), cfc_id' ℝ omega]
      rfl
    rw [Matrix.trace_sub, Complex.sub_re, hf, hF0]
    simp only [hF, g64d_trR_apply, hL, logMat]
    rw [← EReal.coe_neg]
    congr 1
    ring
  have hc2 : Continuous fun s => tau H s σ := by
    have e : (fun s => tau H s σ) = (fun s : ℝ =>
        NormedSpace.exp ((s : ℂ) • (-K)) * σ * NormedSpace.exp ((s : ℂ) • (-(-K)))) := by
      funext s; simp only [g64d_tau_exp, hK, neg_neg]
    rw [e]; exact g64d_conj_cont (-K) σ
  refine ⟨fun t => ?_, fun t ht => ?_⟩
  · rw [hrel, hFTC]; congr 1; ring
  · have e : ev omega (averagedProduction H omega t) =
        t⁻¹ * ∫ s in (0 : ℝ)..t, ev omega (tau H s σ) := by
      show g64d_trR omega _ = _
      rw [averagedProduction, ContinuousLinearMap.map_smul, smul_eq_mul]
      congr 1
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ (hc2.intervalIntegrable 0 t)]
      rfl
    refine ⟨e, ?_⟩
    rw [e, hFTC]
    refine mul_nonneg (inv_nonneg.mpr ht.le) ?_
    rw [hF0, sub_nonneg]
    set V := propagator H (-(-t)) with hV
    have hVs : Vᴴ = propagator H (-t) := by rw [hV, g64d_pstar H hH, neg_neg]
    have hV1 : V * Vᴴ = 1 := by rw [hVs, hV, g64d_padd]; simp [g64d_p0]
    have hV2 : Vᴴ * V = 1 := by rw [hVs, hV, g64d_padd]; simp [g64d_p0]
    have := g64d_klein omega hfaithful V hV1 hV2
    simp only [hF, g64d_trR_apply]
    rw [Matrix.trace_mul_comm omega L, Matrix.trace_mul_comm (evolved H omega t) L]
    have hev2 : evolved H omega t = V * omega * Vᴴ := by rw [hVs]; rfl
    rw [hev2]; exact this
