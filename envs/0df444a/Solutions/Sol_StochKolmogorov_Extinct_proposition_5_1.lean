-- Prove2me | solution 1 for StochKolmogorov.Extinct.proposition_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T00:48:20.770302+00:00
-- url     : https://prove2.me/submissions/797b95e3-957d-401b-ba9c-cccca4110437

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Extinction
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_5
import Theorems.Thm_StochKolmogorov_Persist_kolmogorov_sde_face_invariance
import Theorems.Thm_StochKolmogorov_Persist_lyapunov_moment_bound_mixed_sign
import Theorems.Thm_StochKolmogorov_Persist_log_V_mean_le_occupation_phi_mixed_sign

set_option autoImplicit false
set_option linter.all false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace G51
open StochKolmogorov.Persist EthierKurtz

/-- Second-order Taylor upper bound from an upper bound on the second derivative. -/
theorem taylor_upper (φ : ℝ → ℝ) (θ₁ K : ℝ)
    (hd : ∀ s ∈ Ico (0:ℝ) θ₁, DifferentiableAt ℝ φ s ∧ DifferentiableAt ℝ (deriv φ) s)
    (h2 : ∀ s ∈ Ico (0:ℝ) θ₁, iteratedDeriv 2 φ s ≤ K) :
    ∀ θ ∈ Ico (0:ℝ) θ₁, φ θ ≤ φ 0 + θ * deriv φ 0 + K * θ ^ 2 / 2 := by
  intro θ hθ
  have hsub : Icc 0 θ ⊆ Ico 0 θ₁ := fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 hθ.2⟩
  have h2' : ∀ s ∈ Ico (0:ℝ) θ₁, deriv (deriv φ) s ≤ K := by
    intro s hs
    have := h2 s hs
    rwa [iteratedDeriv_succ, iteratedDeriv_one] at this
  have hD1 : ∀ s ∈ Icc 0 θ, HasDerivAt (fun s => deriv φ s - K * s) (deriv (deriv φ) s - K) s := by
    intro s hs
    exact ((hd s (hsub hs)).2.hasDerivAt.fun_sub ((hasDerivAt_id' s).const_mul K)).congr_deriv
      (by ring)
  have step1 : ∀ s ∈ Icc 0 θ, deriv φ s ≤ deriv φ 0 + K * s := by
    have hanti : AntitoneOn (fun s => deriv φ s - K * s) (Icc 0 θ) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 θ)
      · intro s hs
        exact (hD1 s hs).continuousAt.continuousWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        exact (hD1 s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        rw [(hD1 s (Ioo_subset_Icc_self hs)).deriv]
        linarith [h2' s (hsub (Ioo_subset_Icc_self hs))]
    intro s hs
    have := hanti ⟨le_refl 0, hθ.1⟩ hs hs.1
    simp only [mul_zero, sub_zero] at this
    linarith
  have hD2 : ∀ s ∈ Icc 0 θ, HasDerivAt (fun s => φ s - s * deriv φ 0 - K * s ^ 2 / 2)
      (deriv φ s - deriv φ 0 - K * s) s := by
    intro s hs
    exact (((hd s (hsub hs)).1.hasDerivAt.fun_sub ((hasDerivAt_id' s).mul_const (deriv φ 0))).fun_sub
      (((hasDerivAt_pow 2 s).const_mul K).div_const 2)).congr_deriv (by norm_num <;> ring)
  have hanti2 : AntitoneOn (fun s => φ s - s * deriv φ 0 - K * s ^ 2 / 2) (Icc 0 θ) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 θ)
    · intro s hs
      exact (hD2 s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hD2 s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hD2 s (Ioo_subset_Icc_self hs)).deriv]
      linarith [step1 s (Ioo_subset_Icc_self hs)]
  have := hanti2 ⟨le_refl 0, hθ.1⟩ ⟨hθ.1, le_refl θ⟩ hθ.1
  simp only [zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, zero_div] at this
  linarith

theorem coord_continuous {n : ℕ} (i : Fin n) : Continuous (fun y : SDEState n => y i) := by
  fun_prop

theorem Vfun_measurable {n : ℕ} (c p : SDEState n) : Measurable (Vfun c p) := by
  unfold Vfun
  have hco : ∀ i : Fin n, Measurable (fun y : SDEState n => y i) :=
    fun i => (coord_continuous i).measurable
  refine Measurable.div ?_ ?_
  · exact measurable_const.add (Finset.measurable_sum _ fun i _ => measurable_const.mul (hco i))
  · exact Finset.measurable_prod _ fun i _ => (hco i).pow_const _

theorem Vfun_continuousAt {n : ℕ} (c p x : SDEState n) (hx : x ∈ openOrthant n) :
    ContinuousAt (Vfun c p) x := by
  unfold Vfun
  apply ContinuousAt.div
  · exact (continuous_const.add (continuous_finset_sum _ fun i _ =>
      continuous_const.mul (coord_continuous i))).continuousAt
  · apply tendsto_finset_prod
    intro i _
    exact ((coord_continuous i).continuousAt).rpow_const (Or.inl (hx i).ne')
  · exact (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx i) _).ne'

theorem rpow_eq_exp (v w t : ℝ) (hv : 0 < v) (hw : 0 < w) :
    Real.exp (t * (Real.log v - Real.log w)) = v ^ t * (w ^ t)⁻¹ := by
  rw [Real.rpow_def_of_pos hv, Real.rpow_def_of_pos hw, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

theorem mom_helper {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z f : Ω → ℝ)
    (hZm : AEStronglyMeasurable Z P) (hfm : Measurable f) (t u A : ℝ) (hu : 0 ≤ u) (hA : 0 ≤ A)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hZf : ∀ᵐ ω ∂P, Z ω ≤ f ω ^ t * u)
    (hlin : ∫⁻ ω, ENNReal.ofReal (f ω ^ t) ∂P ≤ ENNReal.ofReal A) :
    Integrable Z P ∧ ∫ ω, Z ω ∂P ≤ A * u := by
  have hle : ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P ≤ ENNReal.ofReal (A * u) := by
    calc ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (f ω ^ t) * ENNReal.ofReal u ∂P := by
          apply lintegral_mono_ae
          filter_upwards [hZf] with ω hω
          rw [← ENNReal.ofReal_mul' hu]
          exact ENNReal.ofReal_le_ofReal hω
      _ = (∫⁻ ω, ENNReal.ofReal (f ω ^ t) ∂P) * ENNReal.ofReal u :=
          lintegral_mul_const _ ((hfm.pow_const t).ennreal_ofReal)
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal u := by gcongr
      _ = ENNReal.ofReal (A * u) := (ENNReal.ofReal_mul hA).symm
  have h0 : 0 ≤ᵐ[P] Z := ae_of_all _ hZ0
  have hfin : HasFiniteIntegral Z P :=
    (hasFiniteIntegral_iff_ofReal h0).2 (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
  refine ⟨⟨hZm, hfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae h0 hZm]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hA hu) hle

theorem abs_le_exp_add (z : ℝ) : |z| ≤ Real.exp z + Real.exp (-z) := by
  have h1 := Real.add_one_le_exp z
  have h2 := Real.add_one_le_exp (-z)
  have h3 := Real.exp_pos z
  have h4 := Real.exp_pos (-z)
  rcases le_total 0 z with h | h
  · rw [abs_of_nonneg h]; linarith
  · rw [abs_of_nonpos h]; linarith

set_option maxHeartbeats 1000000 in
/-- Glue for one exponent vector `q` (Prop. 5.1 / 4.1 pattern): moment bounds for `V_q^δ₀`,
`V_{-q}^δ₀`, the drift bound `E ln V_q(X_T) - ln V_q(x) ≤ -ρT` and Lemma 3.5 give
`E V_q(X_T)^θ ≤ e^{-θρT/2} V_q(x)^θ`. -/
theorem glue_one {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (c q : SDEState n)
    (hc : c ∈ openOrthant n) (R : SDEState n → Prop) (δ₀ H M ρ Te Tmax K₂ θ : ℝ)
    (hδ₀ : 0 < δ₀) (hρ : 0 < ρ) (hTe : 0 < Te) (hK₂ : 0 < K₂)
    (hmeasX : ∀ x ∈ openOrthant n, ∀ t, Measurable (X x t))
    (hface : ∀ x ∈ openOrthant n, ∀ t, ∀ᵐ ω ∂P, X x t ω ∈ openOrthant n)
    (hmom : ∀ x ∈ openOrthant n, ∀ t : ℝ≥0,
      ∫⁻ ω, ENNReal.ofReal (Vfun c q (X x t ω) ^ δ₀) ∂P ≤
        ENNReal.ofReal (Real.exp (δ₀ * H * t) * Vfun c q x ^ δ₀))
    (hhat : ∀ x ∈ openOrthant n, ∀ t : ℝ≥0,
      ∫⁻ ω, ENNReal.ofReal (Vfun c (-q) (X x t ω) ^ δ₀) ∂P ≤
        ENNReal.ofReal (Real.exp (δ₀ * H * t) * Vfun c (-q) x ^ δ₀))
    (hlog : ∀ T : ℝ, T ∈ Icc Te Tmax → ∀ x ∈ openOrthant n, l1 x ≤ M → R x →
      Integrable (fun ω => Real.log (Vfun c q (X x T.toNNReal ω))) P →
      ∫ ω, Real.log (Vfun c q (X x T.toNNReal ω)) ∂P - Real.log (Vfun c q x) ≤ -ρ * T)
    (h35 : ∀ Y : Ω → ℝ,
      Integrable (fun ω => Real.exp (δ₀ * Y ω)) P →
      Integrable (fun ω => Real.exp (-δ₀ * Y ω)) P →
      ∫ ω, Real.exp (δ₀ * Y ω) ∂P + ∫ ω, Real.exp (-δ₀ * Y ω) ∂P ≤
        Real.exp (δ₀ * max H 0 * Tmax) + Real.exp (δ₀ * max H 0 * Tmax) *
          ((1 + (∑ i, c i) * M) ^ 2) ^ δ₀ →
        (∀ θ ∈ Set.Ico 0 (δ₀ / 2), DifferentiableAt ℝ (cgf Y P) θ ∧
          DifferentiableAt ℝ (deriv (cgf Y P)) θ) ∧
        deriv (cgf Y P) 0 = ∫ ω, Y ω ∂P ∧
        ∀ θ ∈ Set.Ico 0 (δ₀ / 2),
          0 ≤ iteratedDeriv 2 (cgf Y P) θ ∧ iteratedDeriv 2 (cgf Y P) θ ≤ K₂)
    (hθ0 : 0 < θ) (hθ1 : θ < δ₀ / 2) (hθ2 : θ * (2 * K₂) ≤ ρ * Te) :
    ∀ T : ℝ, T ∈ Icc Te Tmax → ∀ x ∈ openOrthant n, l1 x ≤ M → R x →
      Integrable (fun ω => Vfun c q (X x T.toNNReal ω) ^ θ) P ∧
      ∫ ω, Vfun c q (X x T.toNNReal ω) ^ θ ∂P ≤
        Real.exp (-(1 / 2) * θ * ρ * T) * Vfun c q x ^ θ := by
  classical
  intro T hT x hx hxM hR
  have hT0 : 0 < T := lt_of_lt_of_le hTe hT.1
  have hA : ∀ y ∈ openOrthant n, 1 ≤ 1 + ∑ i, c i * y i := fun y hy => by
    have : 0 ≤ ∑ i, c i * y i := Finset.sum_nonneg fun i _ => mul_nonneg (hc i).le (hy i).le
    linarith
  have hpi : ∀ y ∈ openOrthant n, 0 < ∏ i, y i ^ q i := fun y hy =>
    Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hy i) _
  have hVheq : ∀ y ∈ openOrthant n,
      Vfun c (-q) y = (1 + ∑ i, c i * y i) * ∏ i, y i ^ q i := by
    intro y hy
    unfold Vfun
    have : ∏ i, y i ^ (-q) i = (∏ i, y i ^ q i)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [show (-q) i = -(q i) by simp, Real.rpow_neg (hy i).le]
    rw [this, div_inv_eq_mul]
  have hVpos : ∀ y ∈ openOrthant n, 0 < Vfun c q y := fun y hy =>
    div_pos (by linarith [hA y hy]) (hpi y hy)
  have hinvle : ∀ y ∈ openOrthant n, (Vfun c q y)⁻¹ ≤ Vfun c (-q) y := by
    intro y hy
    rw [hVheq y hy]
    unfold Vfun
    rw [inv_div]
    calc (∏ i, y i ^ q i) / (1 + ∑ i, c i * y i) ≤ ∏ i, y i ^ q i :=
          div_le_self (hpi y hy).le (hA y hy)
      _ ≤ (1 + ∑ i, c i * y i) * ∏ i, y i ^ q i := le_mul_of_one_le_left (hpi y hy).le (hA y hy)
  have hprod : ∀ y ∈ openOrthant n,
      Vfun c (-q) y * Vfun c q y = (1 + ∑ i, c i * y i) ^ 2 := by
    intro y hy
    rw [hVheq y hy]
    unfold Vfun
    field_simp [(hpi y hy).ne']
  set Cc : ℝ := ∑ i, c i with hCc
  set E0 : ℝ := Real.exp (δ₀ * max H 0 * Tmax) with hE0
  have hE0pos : 0 < E0 := Real.exp_pos _
  have hTT : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT0.le
  have hEt : Real.exp (δ₀ * H * (T.toNNReal : ℝ)) ≤ E0 := by
    apply Real.exp_le_exp.2
    rw [hTT]
    have h1 : H * T ≤ max H 0 * Tmax :=
      calc H * T ≤ max H 0 * T := mul_le_mul_of_nonneg_right (le_max_left _ _) hT0.le
        _ ≤ max H 0 * Tmax := mul_le_mul_of_nonneg_left hT.2 (le_max_right _ _)
    have := mul_le_mul_of_nonneg_left h1 hδ₀.le
    linarith
  have hVx := hVpos x hx
  have hVXm : Measurable (fun ω => Vfun c q (X x T.toNNReal ω)) :=
    (G51.Vfun_measurable c q).comp (hmeasX x hx _)
  obtain ⟨Y, hYdef⟩ : ∃ Y : Ω → ℝ,
      Y = fun ω => Real.log (Vfun c q (X x T.toNNReal ω)) - Real.log (Vfun c q x) := ⟨_, rfl⟩
  have hYm : Measurable Y := by rw [hYdef]; exact (Real.measurable_log.comp hVXm).sub_const _
  have hm1 := G51.mom_helper P (fun ω => Real.exp (δ₀ * Y ω))
    (fun ω => Vfun c q (X x T.toNNReal ω)) (hYm.const_mul δ₀).exp.aestronglyMeasurable hVXm
    δ₀ (Vfun c q x ^ δ₀)⁻¹ (Real.exp (δ₀ * H * (T.toNNReal : ℝ)) * Vfun c q x ^ δ₀)
    (inv_nonneg.2 (Real.rpow_nonneg hVx.le _))
    (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hVx.le _))
    (fun ω => (Real.exp_pos _).le)
    (by
      filter_upwards [hface x hx T.toNNReal] with ω hω
      simp only [hYdef]; rw [G51.rpow_eq_exp _ _ _ (hVpos _ hω) hVx])
    (hmom x hx _)
  have hVhx : 0 < Vfun c (-q) x := by rw [hVheq x hx]; exact mul_pos (by linarith [hA x hx]) (hpi x hx)
  have hVhXm : Measurable (fun ω => Vfun c (-q) (X x T.toNNReal ω)) :=
    (G51.Vfun_measurable c (-q)).comp (hmeasX x hx _)
  have hm2 := G51.mom_helper P (fun ω => Real.exp (-δ₀ * Y ω))
    (fun ω => Vfun c (-q) (X x T.toNNReal ω)) (hYm.const_mul (-δ₀)).exp.aestronglyMeasurable
    hVhXm δ₀ (Vfun c q x ^ δ₀) (Real.exp (δ₀ * H * (T.toNNReal : ℝ)) * Vfun c (-q) x ^ δ₀)
    (Real.rpow_nonneg hVx.le _)
    (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hVhx.le _))
    (fun ω => (Real.exp_pos _).le)
    (by
      filter_upwards [hface x hx T.toNNReal] with ω hω
      have hv := hVpos _ hω
      have e : -δ₀ * Y ω = δ₀ * (Real.log (Vfun c q x) - Real.log (Vfun c q (X x T.toNNReal ω))) := by
        simp only [hYdef]; ring
      rw [e, G51.rpow_eq_exp _ _ _ hVx hv, mul_comm]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hVx.le _)
      rw [← Real.inv_rpow hv.le]
      exact Real.rpow_le_rpow (inv_nonneg.2 hv.le) (hinvle _ hω) hδ₀.le)
    (hhat x hx _)
  have hcx : 1 + ∑ i, c i * x i ≤ 1 + Cc * M := by
    have h1 : ∀ i, c i * x i ≤ c i * l1 x := fun i =>
      mul_le_mul_of_nonneg_left (le_trans (le_abs_self _)
        (Finset.single_le_sum (f := fun j => |x j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)))
        (hc i).le
    have h2 : ∑ i, c i * x i ≤ Cc * l1 x := by
      rw [hCc, Finset.sum_mul]; exact Finset.sum_le_sum fun i _ => h1 i
    have h3 : Cc * l1 x ≤ Cc * M :=
      mul_le_mul_of_nonneg_left hxM (Finset.sum_nonneg fun i _ => (hc i).le)
    linarith
  have hm2b : Real.exp (δ₀ * H * (T.toNNReal : ℝ)) * Vfun c (-q) x ^ δ₀ * Vfun c q x ^ δ₀ ≤
      E0 * ((1 + Cc * M) ^ 2) ^ δ₀ := by
    rw [mul_assoc, ← Real.mul_rpow hVhx.le hVx.le, hprod x hx]
    apply mul_le_mul hEt _ (Real.rpow_nonneg (sq_nonneg _) _) hE0pos.le
    apply Real.rpow_le_rpow (sq_nonneg _) _ hδ₀.le
    exact pow_le_pow_left₀ (by linarith [hA x hx]) hcx 2
  have hm1b : Real.exp (δ₀ * H * (T.toNNReal : ℝ)) * Vfun c q x ^ δ₀ * (Vfun c q x ^ δ₀)⁻¹ ≤ E0 := by
    rw [mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hVx _).ne', mul_one]
    exact hEt
  obtain ⟨hint1, hI1⟩ := hm1
  obtain ⟨hint2, hI2⟩ := hm2
  have hsum : ∫ ω, Real.exp (δ₀ * Y ω) ∂P + ∫ ω, Real.exp (-δ₀ * Y ω) ∂P ≤
      E0 + E0 * ((1 + Cc * M) ^ 2) ^ δ₀ := by linarith
  obtain ⟨hdiff, hd0, hd2⟩ := h35 Y hint1 hint2 hsum
  have hYint : Integrable Y P := by
    refine Integrable.mono' ((hint1.add hint2).div_const δ₀) hYm.aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, le_div_iff₀ hδ₀]
    have := G51.abs_le_exp_add (δ₀ * Y ω)
    rw [abs_mul, abs_of_pos hδ₀, neg_mul_eq_neg_mul] at this
    simpa [mul_comm] using this
  have hlogint : Integrable (fun ω => Real.log (Vfun c q (X x T.toNNReal ω))) P := by
    have : (fun ω => Real.log (Vfun c q (X x T.toNNReal ω))) =
        fun ω => Y ω + Real.log (Vfun c q x) := by
      funext ω; simp only [hYdef]; ring
    rw [this]; exact hYint.add (integrable_const _)
  have hmean : ∫ ω, Y ω ∂P ≤ -ρ * T := by
    have h1 := hlog T hT x hx hxM hR hlogint
    have h2 : ∫ ω, Y ω ∂P =
        ∫ ω, Real.log (Vfun c q (X x T.toNNReal ω)) ∂P - Real.log (Vfun c q x) := by
      simp only [hYdef]
      rw [integral_sub hlogint (integrable_const _)]
      simp
    rw [h2]; exact h1
  have htay := G51.taylor_upper (cgf Y P) (δ₀ / 2) K₂ hdiff (fun s hs => (hd2 s hs).2) θ
    ⟨hθ0.le, hθ1⟩
  have hc0 : cgf Y P 0 = 0 := by simp [cgf, mgf]
  have k2 : ρ * Te ≤ ρ * T := mul_le_mul_of_nonneg_left hT.1 hρ.le
  have k3 : θ * deriv (cgf Y P) 0 ≤ θ * (-ρ * T) :=
    mul_le_mul_of_nonneg_left (by rw [hd0]; exact hmean) hθ0.le
  have k4 : K₂ * θ ^ 2 / 2 ≤ θ * (ρ * T) / 4 := by
    have := mul_le_mul_of_nonneg_left (hθ2.trans k2) hθ0.le
    nlinarith
  have hθρT : 0 ≤ θ * (ρ * T) := by positivity
  have hcgf : cgf Y P θ ≤ -(1 / 2) * θ * ρ * T := by
    rw [hc0] at htay
    nlinarith
  have hintθ : Integrable (fun ω => Real.exp (θ * Y ω)) P := by
    refine Integrable.mono' ((integrable_const 1).add hint1)
      (hYm.const_mul θ).exp.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    show Real.exp (θ * Y ω) ≤ 1 + Real.exp (δ₀ * Y ω)
    rcases le_total 0 (Y ω) with h | h
    · have := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (show θ ≤ δ₀ by linarith) h)
      linarith [zero_lt_one' ℝ]
    · have := Real.exp_le_exp.2 (mul_nonpos_of_nonneg_of_nonpos hθ0.le h)
      rw [Real.exp_zero] at this
      linarith [Real.exp_pos (δ₀ * Y ω)]
  have hmgf : mgf Y P θ ≤ Real.exp (-(1 / 2) * θ * ρ * T) := by
    have hpos : 0 < mgf Y P θ := mgf_pos hintθ
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 hcgf
  have hae : (fun ω => Vfun c q (X x T.toNNReal ω) ^ θ) =ᵐ[P]
      fun ω => Vfun c q x ^ θ * Real.exp (θ * Y ω) := by
    filter_upwards [hface x hx T.toNNReal] with ω hω
    simp only [hYdef]
    rw [G51.rpow_eq_exp _ _ _ (hVpos _ hω) hVx]
    field_simp [(Real.rpow_pos_of_pos hVx θ).ne']
  refine ⟨(hintθ.const_mul _).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_const_mul]
  have : ∫ ω, Real.exp (θ * Y ω) ∂P = mgf Y P θ := rfl
  rw [this, mul_comm]
  exact mul_le_mul_of_nonneg_right hmgf (Real.rpow_nonneg hVx.le θ)

end G51

namespace G53
open EthierKurtz

/-- The same coefficients, read in the `Persist` copy of the model. -/
def toP {n : ℕ} (C : StochKolmogorov.Extinct.Coeffs n) : StochKolmogorov.Persist.Coeffs n :=
  ⟨C.f, C.g, C.Γ⟩

/-- The mixed exponent vector `q^(i)`: `phat` on `S`, `-pcheck` at `i`, `0` elsewhere. -/
noncomputable def qvec {n : ℕ} (S : Finset (Fin n)) (phat : Fin n → ℝ) (pcheck : ℝ) (i : Fin n) :
    SDEState n :=
  WithLp.toLp 2 (fun j => (if j ∈ S then phat j else 0) - (if j = i then pcheck else 0))

theorem qvec_apply {n : ℕ} (S : Finset (Fin n)) (phat : Fin n → ℝ) (pcheck : ℝ) (i j : Fin n) :
    qvec S phat pcheck i j = (if j ∈ S then phat j else 0) - (if j = i then pcheck else 0) := rfl

theorem Ui_eq {n : ℕ} (c : SDEState n) (mu : Measure (SDEState n)) (phat : Fin n → ℝ)
    (pcheck : ℝ) (i : Fin n) (hi : i ∉ StochKolmogorov.Extinct.supp mu) (y : SDEState n)
    (hy : ∀ j, 0 < y j) :
    StochKolmogorov.Extinct.Ui c mu phat pcheck i y =
      StochKolmogorov.Extinct.Vfun c (qvec (StochKolmogorov.Extinct.supp mu) phat pcheck i) y := by
  classical
  set S := StochKolmogorov.Extinct.supp mu with hS
  have h : ∀ j, y j ^ (qvec S phat pcheck i j) =
      (if j ∈ S then y j ^ phat j else 1) / (if j = i then y i ^ pcheck else 1) := by
    intro j
    rw [qvec_apply, Real.rpow_sub (hy j)]
    by_cases h1 : j ∈ S
    · have h2 : j ≠ i := fun h => hi (h ▸ h1)
      simp [h1, h2]
    · by_cases h2 : j = i
      · subst h2; simp [h1]
      · simp [h1, h2]
  have hp : ∏ j, y j ^ (qvec S phat pcheck i j) = (∏ j ∈ S, y j ^ phat j) / y i ^ pcheck := by
    rw [Finset.prod_congr rfl (fun j _ => h j), Finset.prod_div_distrib, Finset.prod_ite_mem,
      Finset.univ_inter]
    simp
  unfold StochKolmogorov.Extinct.Ui StochKolmogorov.Extinct.Vfun
  rw [hp, div_div_eq_mul_div]

theorem Phi_qvec {n : ℕ} (C : StochKolmogorov.Extinct.Coeffs n) (c : SDEState n)
    (S : Finset (Fin n)) (phat : Fin n → ℝ) (pcheck : ℝ) (i : Fin n) (y : SDEState n) :
    StochKolmogorov.Persist.Phi (toP C) c (qvec S phat pcheck i) y =
      StochKolmogorov.Extinct.cBracket C c y -
        ∑ j ∈ S, phat j * (C.f j y - C.sig j j * C.g j y ^ 2 / 2) +
        pcheck * (C.f i y - C.sig i i * C.g i y ^ 2 / 2) := by
  classical
  have e1 : ∀ j z, (toP C).f j z = C.f j z := fun _ _ => rfl
  have e2 : ∀ j z, (toP C).g j z = C.g j z := fun _ _ => rfl
  have e3 : ∀ j k, (toP C).sig j k = C.sig j k := fun _ _ => rfl
  have e4 : StochKolmogorov.Persist.cBracket (toP C) c y = StochKolmogorov.Extinct.cBracket C c y :=
    rfl
  simp only [StochKolmogorov.Persist.Phi, qvec_apply, e1, e2, e3, e4, sub_mul, ite_mul, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

theorem avg_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P] (G : ℝ → Ω → ℝ) (T : ℝ)
    (hT : 0 < T)
    (hG : Integrable (fun z : ℝ × Ω => G z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P)) :
    ∫ z, G z.1 z.2 ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod P) =
      T * ((1 / T) * ∫ t in (0 : ℝ)..T, ∫ ω, G t ω ∂P) := by
  rw [integral_prod _ hG, intervalIntegral.integral_of_le hT.le, integral_Icc_eq_integral_Ioc,
    ← mul_assoc, mul_one_div_cancel hT.ne', one_mul]

open StochKolmogorov.Extinct in
set_option maxHeartbeats 1000000 in
/-- Final assembly of Proposition 5.1 from the mixed moment bound, the mixed log-mean bound,
face invariance and Lemma 3.5. -/
theorem assemble {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (mu : Measure (SDEState n)) (M : ℝ)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀)
    (phat : Fin n → ℝ) (hphat : (∀ i ∈ supp mu, 0 < phat i ∧ phat i < δ₀) ∧
      (∑ i ∈ supp mu, phat i) ≤ δ₀)
    (pcheck : ℝ) (hpcheck : 0 < pcheck ∧ pcheck < δ₀)
    (ρe : ℝ) (hρe : 0 < ρe)
    (ne : ℕ)
    (Te δe : ℝ) (hTe : 0 < Te)
    (h53 : ∀ T : ℝ, T ∈ Set.Icc Te ((ne : ℝ) * Te) →
      ∀ x ∈ orthant n, l1 x ≤ M →
        (∀ i : Fin n, i ∉ supp mu → x i < δe) →
        Integrable (fun q : ℝ × Ω =>
          cBracket C c (X x q.1.toNNReal q.2))
          ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P) ∧
        (∀ j : Fin n, Integrable (fun q : ℝ × Ω =>
          C.f j (X x q.1.toNNReal q.2) -
            C.sig j j * C.g j (X x q.1.toNNReal q.2) ^ 2 / 2)
          ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P)) ∧
        ∀ i : Fin n, i ∉ supp mu →
          cAvg P C X c T x - (∑ j ∈ supp mu, phat j * lyapAvg P C X j T x) +
            pcheck * lyapAvg P C X i T x ≤ -ρe)
    (hFI : ∀ x ∈ openOrthant n, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, X x t ω ∈ openOrthant n)
    (hMIX : ∀ q : SDEState n, (∀ j, |q j| ≤ δ₀) → ∀ x ∈ openOrthant n, ∀ t : ℝ≥0,
      ∫⁻ ω, ENNReal.ofReal (Vfun c q (X x t ω) ^ δ₀) ∂P ≤
        ENNReal.ofReal (Real.exp (δ₀ * Hconst C c γb δ₀ * t) * Vfun c q x ^ δ₀))
    (hLOG : ∀ q : SDEState n, (∀ j, |q j| ≤ δ₀) → ∀ x ∈ openOrthant n, ∀ T : ℝ, 0 < T →
      Integrable (fun z : ℝ × Ω => StochKolmogorov.Persist.Phi (toP C) c q (X x z.1.toNNReal z.2))
        ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P) →
      Integrable (fun ω => Real.log (Vfun c q (X x T.toNNReal ω))) P →
      ∫ ω, Real.log (Vfun c q (X x T.toNNReal ω)) ∂P - Real.log (Vfun c q x) ≤
        ∫ z, StochKolmogorov.Persist.Phi (toP C) c q (X x z.1.toNNReal z.2)
          ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod P))
    (h35 : ∀ K₁ : ℝ, ∃ K₂ : ℝ, 0 < K₂ ∧ ∀ Y : Ω → ℝ,
      Integrable (fun ω => Real.exp (δ₀ * Y ω)) P →
      Integrable (fun ω => Real.exp (-δ₀ * Y ω)) P →
      ∫ ω, Real.exp (δ₀ * Y ω) ∂P + ∫ ω, Real.exp (-δ₀ * Y ω) ∂P ≤ K₁ →
        (∀ θ ∈ Set.Ico 0 (δ₀ / 2), DifferentiableAt ℝ (cgf Y P) θ ∧
          DifferentiableAt ℝ (deriv (cgf Y P)) θ) ∧
        deriv (cgf Y P) 0 = ∫ ω, Y ω ∂P ∧
        ∀ θ ∈ Set.Ico 0 (δ₀ / 2),
          0 ≤ iteratedDeriv 2 (cgf Y P) θ ∧ iteratedDeriv 2 (cgf Y P) θ ≤ K₂) :
    ∃ θ : ℝ, 0 < θ ∧ θ < δ₀ ∧
      ∀ T : ℝ, T ∈ Set.Icc Te ((ne : ℝ) * Te) →
        ∀ x ∈ openOrthant n, l1 x ≤ M →
          (∀ i : Fin n, i ∉ supp mu → x i < δe) →
          Integrable (fun ω => Utheta c mu phat pcheck θ (X x T.toNNReal ω)) P ∧
          ∫ ω, Utheta c mu phat pcheck θ (X x T.toNNReal ω) ∂P ≤
            Real.exp (-(1 / 2) * θ * ρe * T) * Utheta c mu phat pcheck θ x := by
  classical
  haveI : IsProbabilityMeasure P := hX.1
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hd0 : 0 < δ₀ := hδ₀.1
  obtain ⟨K₂, hK₂, hK⟩ := h35 (Real.exp (δ₀ * max (Hconst C c γb δ₀) 0 * ((ne : ℝ) * Te)) +
    Real.exp (δ₀ * max (Hconst C c γb δ₀) 0 * ((ne : ℝ) * Te)) * ((1 + (∑ i, c i) * M) ^ 2) ^ δ₀)
  set θ : ℝ := min (δ₀ / 4) (ρe * Te / (2 * K₂)) with hθdef
  have hθ0 : 0 < θ := lt_min (by linarith) (div_pos (mul_pos hρe hTe) (by linarith))
  have hθ1 : θ < δ₀ / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hθ2 : θ * (2 * K₂) ≤ ρe * Te := by
    have h1 : θ ≤ ρe * Te / (2 * K₂) := min_le_right _ _
    calc θ * (2 * K₂) ≤ ρe * Te / (2 * K₂) * (2 * K₂) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ = ρe * Te := div_mul_cancel₀ _ (by linarith)
  refine ⟨θ, hθ0, by linarith, ?_⟩
  intro T hT x hx hxM hR
  have hmeas : ∀ y ∈ openOrthant n, ∀ t, Measurable (X y t) :=
    fun y hy t => (hX.2.2 y (fun j => (hy j).le)).1 t
  have key : ∀ i ∈ Finset.univ.filter (fun i : Fin n => i ∉ supp mu),
      Integrable (fun ω => Ui c mu phat pcheck i (X x T.toNNReal ω) ^ θ) P ∧
      ∫ ω, Ui c mu phat pcheck i (X x T.toNNReal ω) ^ θ ∂P ≤
        Real.exp (-(1 / 2) * θ * ρe * T) * Ui c mu phat pcheck i x ^ θ := by
    intro i hi
    have hiS : i ∉ supp mu := (Finset.mem_filter.1 hi).2
    have hq : ∀ j, |qvec (supp mu) phat pcheck i j| ≤ δ₀ := by
      intro j
      rw [qvec_apply]
      by_cases h1 : j ∈ supp mu
      · have h2 : j ≠ i := fun h => hiS (h ▸ h1)
        rw [if_pos h1, if_neg h2, sub_zero, abs_of_pos (hphat.1 j h1).1]
        exact (hphat.1 j h1).2.le
      · by_cases h2 : j = i
        · rw [if_neg h1, if_pos h2, zero_sub, abs_neg, abs_of_pos hpcheck.1]
          exact hpcheck.2.le
        · rw [if_neg h1, if_neg h2, sub_zero, abs_zero]; exact hd0.le
    have hq' : ∀ j, |(-qvec (supp mu) phat pcheck i) j| ≤ δ₀ := by
      intro j; rw [PiLp.neg_apply, abs_neg]; exact hq j
    have hlog : ∀ T' : ℝ, T' ∈ Set.Icc Te ((ne : ℝ) * Te) → ∀ y ∈ openOrthant n, l1 y ≤ M →
        (∀ j : Fin n, j ∉ supp mu → y j < δe) →
        Integrable (fun ω => Real.log (Vfun c (qvec (supp mu) phat pcheck i) (X y T'.toNNReal ω))) P →
        ∫ ω, Real.log (Vfun c (qvec (supp mu) phat pcheck i) (X y T'.toNNReal ω)) ∂P -
          Real.log (Vfun c (qvec (supp mu) phat pcheck i) y) ≤ -ρe * T' := by
      intro T' hT' y hy hyM hyR hli
      have hT'0 : 0 < T' := lt_of_lt_of_le hTe hT'.1
      obtain ⟨hcB, hl, havg⟩ := h53 T' hT' y (fun j => (hy j).le) hyM hyR
      have hPhi : (fun z : ℝ × Ω => StochKolmogorov.Persist.Phi (toP C) c
          (qvec (supp mu) phat pcheck i) (X y z.1.toNNReal z.2)) =
          fun z => cBracket C c (X y z.1.toNNReal z.2) -
            ∑ j ∈ supp mu, phat j * (C.f j (X y z.1.toNNReal z.2) -
              C.sig j j * C.g j (X y z.1.toNNReal z.2) ^ 2 / 2) +
            pcheck * (C.f i (X y z.1.toNNReal z.2) -
              C.sig i i * C.g i (X y z.1.toNNReal z.2) ^ 2 / 2) :=
        funext fun z => Phi_qvec C c (supp mu) phat pcheck i _
      have hS : Integrable (fun z : ℝ × Ω => ∑ j ∈ supp mu, phat j * (C.f j (X y z.1.toNNReal z.2) -
              C.sig j j * C.g j (X y z.1.toNNReal z.2) ^ 2 / 2))
          ((volume.restrict (Set.Icc (0 : ℝ) T')).prod P) :=
        integrable_finset_sum _ fun j _ => (hl j).const_mul _
      have hI1 : Integrable (fun z : ℝ × Ω => cBracket C c (X y z.1.toNNReal z.2) -
            ∑ j ∈ supp mu, phat j * (C.f j (X y z.1.toNNReal z.2) -
              C.sig j j * C.g j (X y z.1.toNNReal z.2) ^ 2 / 2))
          ((volume.restrict (Set.Icc (0 : ℝ) T')).prod P) := hcB.sub hS
      have hI2 : Integrable (fun z : ℝ × Ω => pcheck * (C.f i (X y z.1.toNNReal z.2) -
              C.sig i i * C.g i (X y z.1.toNNReal z.2) ^ 2 / 2))
          ((volume.restrict (Set.Icc (0 : ℝ) T')).prod P) := (hl i).const_mul pcheck
      have hI := hI1.add hI2
      have h1 := hLOG _ hq y hy T' hT'0 (by rw [hPhi]; exact hI) hli
      have h2 : ∫ z, StochKolmogorov.Persist.Phi (toP C) c (qvec (supp mu) phat pcheck i)
          (X y z.1.toNNReal z.2) ∂((volume.restrict (Set.Icc (0 : ℝ) T')).prod P) =
          T' * (cAvg P C X c T' y - (∑ j ∈ supp mu, phat j * lyapAvg P C X j T' y) +
            pcheck * lyapAvg P C X i T' y) := by
        rw [hPhi, integral_add hI1 hI2, integral_sub hcB hS,
          integral_finset_sum _ fun j _ => (hl j).const_mul _, integral_const_mul]
        simp only [integral_const_mul]
        rw [avg_eq P (fun t ω => cBracket C c (X y t.toNNReal ω)) T' hT'0 hcB,
          avg_eq P (fun t ω => C.f i (X y t.toNNReal ω) -
            C.sig i i * C.g i (X y t.toNNReal ω) ^ 2 / 2) T' hT'0 (hl i)]
        rw [Finset.sum_congr rfl fun j _ => by
          rw [avg_eq P (fun t ω => C.f j (X y t.toNNReal ω) -
            C.sig j j * C.g j (X y t.toNNReal ω) ^ 2 / 2) T' hT'0 (hl j)]]
        unfold cAvg lyapAvg
        rw [mul_add, mul_sub, Finset.mul_sum]
        congr 1
        · congr 1
          refine Finset.sum_congr rfl fun j _ => by ring
        · ring
      have h3 := havg i hiS
      calc _ ≤ _ := h1
        _ = _ := h2
        _ ≤ T' * (-ρe) := mul_le_mul_of_nonneg_left h3 hT'0.le
        _ = -ρe * T' := by ring
    have hg := G51.glue_one P X c (qvec (supp mu) phat pcheck i) hc
      (fun y => ∀ j : Fin n, j ∉ supp mu → y j < δe) δ₀ (Hconst C c γb δ₀) M ρe Te
      ((ne : ℝ) * Te) K₂ θ hd0 hρe hTe hK₂ hmeas hFI (hMIX _ hq) (hMIX _ hq') hlog hK
      hθ0 hθ1 hθ2 T hT x hx hxM hR
    have hae : (fun ω => Ui c mu phat pcheck i (X x T.toNNReal ω) ^ θ) =ᵐ[P]
        fun ω => Vfun c (qvec (supp mu) phat pcheck i) (X x T.toNNReal ω) ^ θ := by
      filter_upwards [hFI x hx T.toNNReal] with ω hω
      rw [Ui_eq c mu phat pcheck i hiS _ hω]
    refine ⟨hg.1.congr hae.symm, ?_⟩
    rw [integral_congr_ae hae, Ui_eq c mu phat pcheck i hiS x hx]
    exact hg.2
  unfold Utheta
  refine ⟨integrable_finset_sum _ fun i hi => (key i hi).1, ?_⟩
  rw [integral_finset_sum _ fun i hi => (key i hi).1, Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => (key i hi).2

end G53

open StochKolmogorov.Extinct EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (mu : Measure (SDEState n)) (h13 : Assumption13 P C X mu)
    (M : ℝ) (hM : IsRadiusM C c γb M)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀)
    (phat : Fin n → ℝ) (hphat : (∀ i ∈ supp mu, 0 < phat i ∧ phat i < δ₀) ∧
      (∑ i ∈ supp mu, phat i) ≤ δ₀)
    (pcheck : ℝ) (hpcheck : 0 < pcheck ∧ pcheck < δ₀)
    (ρe : ℝ) (hρe : 0 < ρe)
    (ne : ℕ) (hne : Hconst C c γb δ₀ < γb * ((ne : ℝ) - 1))
    (Te δe : ℝ) (hTe : 0 < Te) (hδe : 0 < δe)
    (h53 : ∀ T : ℝ, T ∈ Set.Icc Te ((ne : ℝ) * Te) →
      ∀ x ∈ orthant n, l1 x ≤ M →
        (∀ i : Fin n, i ∉ supp mu → x i < δe) →
        Integrable (fun q : ℝ × Ω =>
          cBracket C c (X x q.1.toNNReal q.2))
          ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P) ∧
        (∀ j : Fin n, Integrable (fun q : ℝ × Ω =>
          C.f j (X x q.1.toNNReal q.2) -
            C.sig j j * C.g j (X x q.1.toNNReal q.2) ^ 2 / 2)
          ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P)) ∧
        ∀ i : Fin n, i ∉ supp mu →
          cAvg P C X c T x - (∑ j ∈ supp mu, phat j * lyapAvg P C X j T x) +
            pcheck * lyapAvg P C X i T x ≤ -ρe) :
    ∃ θ : ℝ, 0 < θ ∧ θ < δ₀ ∧
      ∀ T : ℝ, T ∈ Set.Icc Te ((ne : ℝ) * Te) →
        ∀ x ∈ openOrthant n, l1 x ≤ M →
          (∀ i : Fin n, i ∉ supp mu → x i < δe) →
          Integrable (fun ω => Utheta c mu phat pcheck θ (X x T.toNNReal ω)) P ∧
          ∫ ω, Utheta c mu phat pcheck θ (X x T.toNNReal ω) ∂P ≤
            Real.exp (-(1 / 2) * θ * ρe * T) * Utheta c mu phat pcheck θ x := by
  obtain ⟨hP, hB, hsol⟩ := id hX
  haveI := hP
  have hC : ∀ i, LocallyLipschitzOn (StochKolmogorov.Persist.orthant n) ((G53.toP C).f i) ∧
      LocallyLipschitzOn (StochKolmogorov.Persist.orthant n) ((G53.toP C).g i) := hA.2.1
  have hδP : StochKolmogorov.Persist.IsDelta0 (G53.toP C) γb δ₀ :=
    ⟨hδ₀.1, lt_of_lt_of_le hδ₀.2.1 (min_le_left _ _), hδ₀.2.2⟩
  have hFI : ∀ x ∈ openOrthant n, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, X x t ω ∈ openOrthant n := by
    intro x hx t
    have hxf : x ∈ StochKolmogorov.Persist.faceOpen (Finset.univ : Finset (Fin n)) :=
      ⟨fun i => (hx i).le, fun i hi => absurd (Finset.mem_univ i) hi, fun i _ => hx i⟩
    filter_upwards [StochKolmogorov.Persist.kolmogorov_sde_face_invariance (P := P) (G53.toP C)
      hB hC hxf (hsol x (fun i => (hx i).le))] with ω hω
    exact fun i => (hω t).2.2 i (Finset.mem_univ i)
  exact G53.assemble P C B X hX c γb hA mu M δ₀ hδ₀ phat hphat pcheck hpcheck ρe hρe ne Te δe hTe
    h53 hFI
    (fun q hq x hx t => StochKolmogorov.Persist.lyapunov_moment_bound_mixed_sign hn P (G53.toP C)
      B X hX c γb hA δ₀ hδP q hq x hx t)
    (fun q hq x hx T hT hPi hli =>
      StochKolmogorov.Persist.log_V_mean_le_occupation_phi_mixed_sign hn P (G53.toP C) B X hX c γb
        hA δ₀ hδP q hq x hx T hT hPi hli)
    (fun K₁ => by
      obtain ⟨K₂, hK₂, hK⟩ := StochKolmogorov.Persist.lemma_3_5 δ₀ hδ₀.1 K₁
      exact ⟨K₂, hK₂, fun Y => hK P Y⟩)
