-- Prove2me | solution 1 for QED.covariantD_gauge_covariant
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T22:33:53.862767+00:00
-- url     : https://prove2.me/submissions/28c01ba3-086e-4a8b-af87-3ae6465957ad

import Definitions.Def_QED_fields

open QED

/-! ## Gamma matrices -/

theorem W3a_QED_g0 : diracGamma 0 = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := rfl
theorem W3a_QED_g1 : diracGamma 1 = !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0] := rfl
theorem W3a_QED_g2 : diracGamma 2 = !![0, 0, 0, -Complex.I; 0, 0, Complex.I, 0;
    0, Complex.I, 0, 0; -Complex.I, 0, 0, 0] := rfl
theorem W3a_QED_g3 : diracGamma 3 = !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0] := rfl

set_option maxHeartbeats 4000000 in
theorem W3a_QED_diracGamma_isDiracRepresentation : IsDiracRepresentation diracGamma := by
  constructor
  · intro μ ν
    fin_cases μ <;> fin_cases ν <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [W3a_QED_g0, W3a_QED_g1, W3a_QED_g2, W3a_QED_g3, minkowski, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.one_apply] <;> ring_nf <;> simp
  · intro μ
    fin_cases μ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [W3a_QED_g0, W3a_QED_g1, W3a_QED_g2, W3a_QED_g3, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.conjTranspose_apply]

/-! ## Reality of the current -/

theorem W3a_QED_current_isReal (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hγ : IsDiracRepresentation γ)
    (ψ : SpinorField) (μ : Fin 4) (x : Spacetime) :
    diracPairing γ (γ μ) (ψ x) (ψ x) = (current γ ψ μ x : ℂ) := by
  have h00 : γ 0 * γ 0 = 1 := by
    have h := hγ.1 0 0
    rw [show (2 * (minkowski 0 0 : ℂ)) = 2 by simp [minkowski], ← two_smul ℂ (γ 0 * γ 0)] at h
    exact smul_right_injective _ (two_ne_zero) h
  have hM : (γ 0 * γ μ).conjTranspose = γ 0 * γ μ := by
    calc (γ 0 * γ μ).conjTranspose = (γ μ).conjTranspose * (γ 0).conjTranspose :=
          Matrix.conjTranspose_mul _ _
      _ = (γ 0 * γ μ * γ 0) * (γ 0 * γ 0 * γ 0) := by rw [hγ.2 μ, hγ.2 0]
      _ = γ 0 * γ μ * ((γ 0 * γ 0) * (γ 0 * γ 0)) := by simp only [Matrix.mul_assoc]
      _ = γ 0 * γ μ := by rw [h00, Matrix.mul_one, Matrix.mul_one]
  have hMij : ∀ i j, (starRingEnd ℂ) ((γ 0 * γ μ) i j) = (γ 0 * γ μ) j i := by
    intro i j
    have := congrFun (congrFun hM j) i
    rw [Matrix.conjTranspose_apply] at this
    exact this
  have hconj : (starRingEnd ℂ) (diracPairing γ (γ μ) (ψ x) (ψ x))
      = diracPairing γ (γ μ) (ψ x) (ψ x) := by
    unfold diracPairing
    simp_rw [map_sum, map_mul, Complex.conj_conj, hMij]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold current
  exact (Complex.conj_eq_iff_re.mp hconj).symm

/-! ## Partial derivative calculus -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem W3a_QED_pd_add {f g : Spacetime → E} {x : Spacetime} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (a : Fin 4) :
    partialD a (fun y => f y + g y) x = partialD a f x + partialD a g x := by
  unfold partialD; rw [fderiv_fun_add hf hg]; rfl

theorem W3a_QED_pd_sub {f g : Spacetime → E} {x : Spacetime} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (a : Fin 4) :
    partialD a (fun y => f y - g y) x = partialD a f x - partialD a g x := by
  unfold partialD; rw [fderiv_fun_sub hf hg]; rfl

theorem W3a_QED_pd_comm {f : Spacetime → E} (hf2 : ContDiff ℝ 2 f) (i j : Fin 4)
    (x : Spacetime) : partialD i (partialD j f) x = partialD j (partialD i f) x := by
  unfold partialD
  have hC1 : ContDiff ℝ 1 (fderiv ℝ f) := hf2.fderiv_right (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ f) := hC1.differentiable (by norm_num)
  rw [fderiv_clm_apply (hD x) (differentiableAt_const _),
    fderiv_clm_apply (hD x) (differentiableAt_const _)]
  simp
  exact (hf2.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness])) _ _

theorem W3a_QED_pd_diff {f : Spacetime → E} (hf2 : ContDiff ℝ 2 f) (b : Fin 4) :
    Differentiable ℝ (partialD b f) := by
  have hC1 : ContDiff ℝ 1 (fderiv ℝ f) := hf2.fderiv_right (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ f) := hC1.differentiable (by norm_num)
  intro y
  exact (hD y).clm_apply (differentiableAt_const _)

end

theorem W3a_QED_pd_cmul (c : ℝ) {g : Spacetime → ℝ} {x : Spacetime}
    (hg : DifferentiableAt ℝ g x) (a : Fin 4) :
    partialD a (fun y => c * g y) x = c * partialD a g x := by
  unfold partialD; rw [(hg.hasFDerivAt.const_mul c).fderiv]; rfl

theorem W3a_QED_pd_cmul_sub (c : ℝ) {f g : Spacetime → ℝ} {x : Spacetime}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (a : Fin 4) :
    partialD a (fun y => c * (f y - g y)) x = c * (partialD a f x - partialD a g x) := by
  have h : HasFDerivAt (fun y => c * (f y - g y)) (c • (fderiv ℝ f x - fderiv ℝ g x)) x :=
    (hf.hasFDerivAt.sub hg.hasFDerivAt).const_mul c
  unfold partialD; rw [h.fderiv]; rfl

theorem W3a_QED_pd_sum_cmul (c : Fin 4 → ℝ) (g : Fin 4 → Spacetime → ℝ) {x : Spacetime}
    (hg : ∀ i, DifferentiableAt ℝ (g i) x) (a : Fin 4) :
    partialD a (fun y => ∑ i, c i * g i y) x = ∑ i, c i * partialD a (g i) x := by
  have h : HasFDerivAt (fun y => ∑ i, c i * g i y) (∑ i, c i • fderiv ℝ (g i) x) x :=
    HasFDerivAt.fun_sum (fun i _ => (hg i).hasFDerivAt.const_mul (c i))
  unfold partialD; rw [h.fderiv]
  simp [ContinuousLinearMap.sum_apply]

theorem W3a_QED_pd_const (a : Fin 4) (x : Spacetime) :
    partialD a (fun _ : Spacetime => (0 : ℝ)) x = 0 := by
  simp [partialD]

/-! ## Field strength -/

theorem W3a_QED_fieldStrength_gauge_invariant (A : GaugeField) (χ : Spacetime → ℝ)
    (hA : ContDiff ℝ 1 A) (hχ : ContDiff ℝ 2 χ) (μ ν : Fin 4) (x : Spacetime) :
    fieldStrength (gaugeShift χ A) μ ν x = fieldStrength A μ ν x := by
  have hAd : ∀ i, Differentiable ℝ (fun y => A y i) := fun i =>
    (contDiff_pi.mp hA i).differentiable (by norm_num)
  have hχd : ∀ b, Differentiable ℝ (partialD b χ) := fun b => W3a_QED_pd_diff hχ b
  simp only [fieldStrength, gaugeShift]
  rw [W3a_QED_pd_add (hAd ν x) (hχd ν x), W3a_QED_pd_add (hAd μ x) (hχd μ x),
    W3a_QED_pd_comm hχ μ ν x]
  ring

theorem W3a_QED_fieldStrength_bianchi (A : GaugeField) (hA : ContDiff ℝ 2 A)
    (lam μ ν : Fin 4) (x : Spacetime) :
    partialD lam (fun y => fieldStrength A μ ν y) x
      + partialD μ (fun y => fieldStrength A ν lam y) x
      + partialD ν (fun y => fieldStrength A lam μ y) x = 0 := by
  have hAi : ∀ i, ContDiff ℝ 2 (fun y => A y i) := fun i => contDiff_pi.mp hA i
  have dA : ∀ b i, Differentiable ℝ (partialD b (fun y => A y i)) := fun b i =>
    W3a_QED_pd_diff (hAi i) b
  have sym : ∀ a b i, partialD a (partialD b (fun y => A y i)) x
      = partialD b (partialD a (fun y => A y i)) x := fun a b i => W3a_QED_pd_comm (hAi i) a b x
  simp only [fieldStrength]
  rw [W3a_QED_pd_sub (dA μ ν x) (dA ν μ x), W3a_QED_pd_sub (dA ν lam x) (dA lam ν x),
    W3a_QED_pd_sub (dA lam μ x) (dA μ lam x)]
  linear_combination sym lam μ ν + sym ν lam μ + sym μ ν lam

/-! ## Gauge covariance -/

theorem solution (e : ℝ) (A : GaugeField) (ψ : SpinorField)
    (χ : Spacetime → ℝ) (hχ : ContDiff ℝ 1 χ) (hψ : ContDiff ℝ 1 ψ)
    (μ : Fin 4) (x : Spacetime) :
    covariantD e (gaugeShift χ A) (gaugePhase e χ ψ) μ x
      = Complex.exp (-(Complex.I * (e : ℂ) * (χ x : ℂ))) • covariantD e A ψ μ x := by
  have hχd : Differentiable ℝ χ := hχ.differentiable (by norm_num)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hof : HasFDerivAt (fun y => ((χ y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ χ x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (hχd x).hasFDerivAt
  have hc := ((hof.const_mul (Complex.I * (e : ℂ))).neg).cexp
  have hp : HasFDerivAt (gaugePhase e χ ψ) _ x := hc.smul (hψd x).hasFDerivAt
  simp only [covariantD]
  unfold partialD
  rw [hp.fderiv]
  simp only [gaugeShift, gaugePhase, partialD]
  ext i
  simp
  ring

theorem W3a_QED_pairing_smul (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (M : Matrix (Fin 4) (Fin 4) ℂ) (c : ℂ) (φ χ : Fin 4 → ℂ) :
    diracPairing γ M (c • φ) (c • χ) = ((starRingEnd ℂ) c * c) * diracPairing γ M φ χ := by
  unfold diracPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem W3a_QED_lagrangian_gauge_invariant (m e : ℝ) (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (A : GaugeField) (ψ : SpinorField) (χ : Spacetime → ℝ)
    (hA : ContDiff ℝ 1 A) (hχ : ContDiff ℝ 2 χ) (hψ : ContDiff ℝ 1 ψ) (x : Spacetime) :
    lagrangian m e γ (gaugeShift χ A) (gaugePhase e χ ψ) x = lagrangian m e γ A ψ x := by
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by norm_num)
  have hF : ∀ μ ν, fieldStrength (gaugeShift χ A) μ ν x = fieldStrength A μ ν x :=
    fun μ ν => W3a_QED_fieldStrength_gauge_invariant A χ hA hχ μ ν x
  have hFup : ∀ μ ν, fieldStrengthUp (gaugeShift χ A) μ ν x = fieldStrengthUp A μ ν x := by
    intro μ ν
    simp only [fieldStrengthUp, hF]
  have hcc : (starRingEnd ℂ) (Complex.exp (-(Complex.I * (e : ℂ) * (χ x : ℂ))))
      * Complex.exp (-(Complex.I * (e : ℂ) * (χ x : ℂ))) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    rw [show (starRingEnd ℂ) (-(Complex.I * (e : ℂ) * (χ x : ℂ)))
        + -(Complex.I * (e : ℂ) * (χ x : ℂ)) = 0 by
      simp [Complex.conj_ofReal] <;> ring]
    exact Complex.exp_zero
  unfold lagrangian
  simp only [hF, hFup, solution e A ψ χ hχ1 hψ]
  have hph : gaugePhase e χ ψ x = Complex.exp (-(Complex.I * (e : ℂ) * (χ x : ℂ))) • ψ x := rfl
  simp only [hph, W3a_QED_pairing_smul, hcc, one_mul]

/-! ## Lorenz gauge wave equation -/

theorem W3a_QED_gaugeUp_diag (A : GaugeField) (ν : Fin 4) (y : Spacetime) :
    gaugeUp A ν y = minkowski ν ν * A y ν := by
  unfold gaugeUp
  rw [Finset.sum_eq_single ν (fun b _ hb => by simp [minkowski, Ne.symm hb]) (by simp)]

theorem W3a_QED_fieldStrengthUp_diag (A : GaugeField) (μ ν : Fin 4) (y : Spacetime) :
    fieldStrengthUp A μ ν y = minkowski μ μ * minkowski ν ν * fieldStrength A μ ν y := by
  unfold fieldStrengthUp
  rw [Finset.sum_eq_single μ (fun b _ hb => by simp [minkowski, Ne.symm hb]) (by simp)]
  rw [Finset.sum_eq_single ν (fun b _ hb => by simp [minkowski, Ne.symm hb]) (by simp)]

theorem W3a_QED_dAlembert_diag (f : Spacetime → ℝ) (x : Spacetime) :
    dAlembert f x = ∑ μ, minkowski μ μ * partialD μ (partialD μ f) x := by
  unfold dAlembert
  apply Finset.sum_congr rfl
  intro μ _
  rw [Finset.sum_eq_single μ (fun b _ hb => by simp [minkowski, Ne.symm hb]) (by simp)]
  rfl

theorem W3a_QED_lorenz_wave_equation (e : ℝ) (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (A : GaugeField) (ψ : SpinorField) (hA : ContDiff ℝ 2 A)
    (hM : IsMaxwellSolution e γ A ψ) (hL : LorenzGauge A) (ν : Fin 4) (x : Spacetime) :
    dAlembert (fun y => gaugeUp A ν y) x = e * current γ ψ ν x := by
  have hAi : ∀ i, ContDiff ℝ 2 (fun y => A y i) := fun i => contDiff_pi.mp hA i
  have hAd : ∀ i, Differentiable ℝ (fun y => A y i) := fun i =>
    (hAi i).differentiable (by norm_num)
  have dA : ∀ b i, Differentiable ℝ (partialD b (fun y => A y i)) := fun b i =>
    W3a_QED_pd_diff (hAi i) b
  have sym : ∀ a b i, partialD a (partialD b (fun y => A y i)) x
      = partialD b (partialD a (fun y => A y i)) x := fun a b i => W3a_QED_pd_comm (hAi i) a b x
  -- left-hand side
  have hg : (fun y => gaugeUp A ν y) = fun y => minkowski ν ν * A y ν :=
    funext fun y => W3a_QED_gaugeUp_diag A ν y
  have key : ∀ μ, partialD μ (partialD μ (fun y => minkowski ν ν * A y ν)) x
      = minkowski ν ν * partialD μ (partialD μ (fun y => A y ν)) x := by
    intro μ
    have h1 : partialD μ (fun y => minkowski ν ν * A y ν)
        = fun y => minkowski ν ν * partialD μ (fun y => A y ν) y :=
      funext fun y => W3a_QED_pd_cmul _ (hAd ν y) μ
    rw [h1, W3a_QED_pd_cmul _ (dA μ ν x) μ]
  have hLHS : dAlembert (fun y => gaugeUp A ν y) x
      = ∑ μ, minkowski μ μ * (minkowski ν ν * partialD μ (partialD μ (fun y => A y ν)) x) := by
    rw [hg, W3a_QED_dAlembert_diag]
    exact Finset.sum_congr rfl fun μ _ => by rw [key]
  -- Maxwell
  have hMx := hM ν x
  have hRHS : ∀ μ, partialD μ (fun y => fieldStrengthUp A μ ν y) x
      = minkowski μ μ * minkowski ν ν * (partialD μ (partialD μ (fun y => A y ν)) x
          - partialD μ (partialD ν (fun y => A y μ)) x) := by
    intro μ
    have h1 : (fun y => fieldStrengthUp A μ ν y) = fun y => minkowski μ μ * minkowski ν ν *
        (partialD μ (fun y => A y ν) y - partialD ν (fun y => A y μ) y) :=
      funext fun y => by rw [W3a_QED_fieldStrengthUp_diag]; rfl
    rw [h1, W3a_QED_pd_cmul_sub _ (dA μ ν x) (dA ν μ x)]
  simp only [hRHS] at hMx
  -- Lorenz
  have hz : (fun y => ∑ μ, minkowski μ μ * partialD μ (fun y => A y μ) y) = fun _ => 0 := by
    funext y
    rw [← hL y]
    apply Finset.sum_congr rfl
    intro μ _
    rw [Finset.sum_eq_single μ (fun b _ hb => by simp [minkowski, Ne.symm hb]) (by simp)]
  have hLz : partialD ν (fun y => ∑ μ, minkowski μ μ * partialD μ (fun y => A y μ) y) x
      = ∑ μ, minkowski μ μ * partialD ν (partialD μ (fun y => A y μ)) x :=
    W3a_QED_pd_sum_cmul (fun μ => minkowski μ μ) (fun μ => partialD μ (fun y => A y μ))
      (fun μ => dA μ μ x) ν
  rw [hz, W3a_QED_pd_const] at hLz
  have hL2 : ∑ μ, minkowski μ μ * partialD μ (partialD ν (fun y => A y μ)) x = 0 := by
    rw [hLz]
    exact Finset.sum_congr rfl fun μ _ => by rw [sym]
  rw [hLHS]
  simp only [Fin.sum_univ_four] at hMx hL2 ⊢
  linear_combination hMx + minkowski ν ν * hL2

/-! ## Current conservation -/

theorem W3a_QED_gamma_facts (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hγ : IsDiracRepresentation γ) :
    (∀ i j, star ((γ 0) i j) = (γ 0) j i) ∧
      ∀ μ, ∀ i j, star ((γ 0 * γ μ) i j) = (γ 0 * γ μ) j i := by
  have h00 : γ 0 * γ 0 = 1 := by
    have h := hγ.1 0 0
    rw [show (2 * (minkowski 0 0 : ℂ)) = 2 by simp [minkowski], ← two_smul ℂ (γ 0 * γ 0)] at h
    exact smul_right_injective _ (two_ne_zero) h
  have hg0 : (γ 0).conjTranspose = γ 0 := by
    rw [hγ.2 0, h00, Matrix.one_mul]
  have hM : ∀ μ, (γ 0 * γ μ).conjTranspose = γ 0 * γ μ := by
    intro μ
    calc (γ 0 * γ μ).conjTranspose = (γ μ).conjTranspose * (γ 0).conjTranspose :=
          Matrix.conjTranspose_mul _ _
      _ = (γ 0 * γ μ * γ 0) * γ 0 := by rw [hγ.2 μ, hg0]
      _ = γ 0 * γ μ * (γ 0 * γ 0) := by simp only [Matrix.mul_assoc]
      _ = γ 0 * γ μ := by rw [h00, Matrix.mul_one]
  refine ⟨fun i j => ?_, fun μ i j => ?_⟩
  · have := congrFun (congrFun hg0 j) i
    rw [Matrix.conjTranspose_apply] at this
    exact this
  · have := congrFun (congrFun (hM μ) j) i
    rw [Matrix.conjTranspose_apply] at this
    exact this

theorem W3a_QED_herm_real (N : Matrix (Fin 4) (Fin 4) ℂ) (hN : ∀ i j, star (N i j) = N j i)
    (u : Fin 4 → ℂ) : (star u ⬝ᵥ (Matrix.mulVec N u)).im = 0 := by
  have h : star (star u ⬝ᵥ (Matrix.mulVec N u)) = star u ⬝ᵥ (Matrix.mulVec N u) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, hN,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  exact Complex.conj_eq_iff_im.mp h

theorem W3a_QED_part1 (N : Matrix (Fin 4) (Fin 4) ℂ) (u z : Fin 4 → ℂ) :
    ∑ i, ∑ j, star (u i) * N i j * z j = star u ⬝ᵥ (Matrix.mulVec N z) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]

theorem W3a_QED_part2 (N : Matrix (Fin 4) (Fin 4) ℂ) (hN : ∀ i j, star (N i j) = N j i)
    (u z : Fin 4 → ℂ) :
    ∑ i, ∑ j, u j * (N i j * star (z i)) = star (star u ⬝ᵥ (Matrix.mulVec N z)) := by
  rw [← W3a_QED_part1]
  simp only [star_sum, star_mul', star_star, hN]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem W3a_QED_current_conservation (m e : ℝ) (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hγ : IsDiracRepresentation γ) (A : GaugeField) (ψ : SpinorField)
    (hψ : ContDiff ℝ 1 ψ) (hD : IsDiracSolution m e γ A ψ) (x : Spacetime) :
    (∑ μ : Fin 4, partialD μ (fun y => current γ ψ μ y) x) = 0 := by
  obtain ⟨hg0, hN⟩ := W3a_QED_gamma_facts γ hγ
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hcomp : ∀ i, HasFDerivAt (fun y => ψ y i)
      ((ContinuousLinearMap.proj i).comp (fderiv ℝ ψ x)) x :=
    fun i => hasFDerivAt_pi'.1 (hψd x).hasFDerivAt i
  have key : ∀ μ, partialD μ (fun y => current γ ψ μ y) x
      = (∑ i, ∑ j, (star (ψ x i) * (γ 0 * γ μ) i j * partialD μ ψ x j
          + ψ x j * ((γ 0 * γ μ) i j * star (partialD μ ψ x i)))).re := by
    intro μ
    have hP : HasFDerivAt (fun y => ∑ i, ∑ j, star (ψ y i) * (γ 0 * γ μ) i j * ψ y j) _ x :=
      HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ =>
        ((hcomp i).star.mul_const ((γ 0 * γ μ) i j)).mul (hcomp j)
    have hJ : HasFDerivAt (fun y => current γ ψ μ y) _ x :=
      Complex.reCLM.hasFDerivAt.comp x hP
    rw [show partialD μ (fun y => current γ ψ μ y) x
      = fderiv ℝ (fun y => current γ ψ μ y) x (Pi.single μ 1) from rfl, hJ.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
      Complex.reCLM_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearEquiv.coe_coe, starL'_apply,
      ContinuousLinearMap.proj_apply] <;> rfl
  have key2 : ∀ μ, partialD μ (fun y => current γ ψ μ y) x
      = 2 * (star (ψ x) ⬝ᵥ (Matrix.mulVec (γ 0) (Matrix.mulVec (γ μ) (partialD μ ψ x)))).re := by
    intro μ
    rw [key, Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib), Finset.sum_add_distrib,
      W3a_QED_part1, W3a_QED_part2 _ (hN μ), Matrix.mulVec_mulVec, Complex.add_re,
      Complex.star_def, Complex.conj_re]
    ring
  have hr : ∀ μ, (star (ψ x) ⬝ᵥ (Matrix.mulVec (γ 0) (Matrix.mulVec (γ μ) (ψ x)))).im = 0 := by
    intro μ
    rw [Matrix.mulVec_mulVec]
    exact W3a_QED_herm_real _ (hN μ) _
  have hr0 : (star (ψ x) ⬝ᵥ (Matrix.mulVec (γ 0) (ψ x))).im = 0 := W3a_QED_herm_real _ hg0 _
  have E := congrArg (fun z => star (ψ x) ⬝ᵥ (Matrix.mulVec (γ 0) z)) (hD x)
  simp only [covariantD, Matrix.mulVec_sum, dotProduct_sum, Matrix.mulVec_smul, dotProduct_smul,
    Matrix.mulVec_add, dotProduct_add, smul_eq_mul] at E
  have Eim := congrArg Complex.im E
  simp [Complex.mul_im, Complex.mul_re, hr0] at Eim
  have hr' : ∀ μ, (star (ψ x) ⬝ᵥ Matrix.mulVec (γ 0 * γ μ) (ψ x)).im = 0 := by
    intro μ
    rw [← Matrix.mulVec_mulVec]
    exact hr μ
  have Eim2 : ∑ μ, (star (ψ x) ⬝ᵥ Matrix.mulVec (γ 0 * γ μ) (partialD μ ψ x)).re = 0 := by
    rw [← Eim]
    apply Finset.sum_congr rfl
    intro μ _
    rw [hr' μ]
    ring
  rw [Finset.sum_congr rfl (fun μ _ => key2 μ), ← Finset.mul_sum]
  simp only [Matrix.mulVec_mulVec]
  rw [Eim2, mul_zero]

theorem W3a_QED_qed_field_equations (m e : ℝ) (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hγ : IsDiracRepresentation γ) (A : GaugeField) (ψ : SpinorField)
    (hA : ContDiff ℝ 2 A) (hψ : ContDiff ℝ 1 ψ)
    (hD : IsDiracSolution m e γ A ψ) (hM : IsMaxwellSolution e γ A ψ)
    (hL : LorenzGauge A) :
    (∀ (ν : Fin 4) (x : Spacetime),
        dAlembert (fun y => gaugeUp A ν y) x = e * current γ ψ ν x) ∧
      (∀ x : Spacetime, (∑ ν : Fin 4, partialD ν (fun y => current γ ψ ν y) x) = 0) :=
  ⟨fun ν x => W3a_QED_lorenz_wave_equation e γ A ψ hA hM hL ν x,
    fun x => W3a_QED_current_conservation m e γ hγ A ψ hψ hD x⟩
