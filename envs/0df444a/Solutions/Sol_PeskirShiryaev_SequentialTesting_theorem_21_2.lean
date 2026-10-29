-- Prove2me | solution 1 for PeskirShiryaev.SequentialTesting.theorem_21_2
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T05:21:15.317982+00:00
-- url     : https://prove2.me/submissions/34daa5e3-48f5-4e56-b697-f4d3fa374c66

import Definitions.Def_PeskirShiryaev_SequentialTesting_BoundaryClass
import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace PS_t212_aux

noncomputable def Y : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := brownian

lemma Y_spec : (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[gaussianLimit] preBrownian t)
      ∧ ∀ ω t (β : ℝ≥0) (_ : 0 < β) (_ : β < ⨆ n, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ))),
        ∃ U ∈ nhds t, ∃ C, HolderOnWith C β (Y · ω) U :=
  isPreBrownianReal_preBrownian.exists_continuous_modification.choose_spec

lemma Y_cont (ω : ℝ≥0 → ℝ) : Continuous (fun t => Y t ω) := by
  have hpos : (0 : ℝ) < ⨆ n : ℕ, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ)) := by
    have hb : BddAbove (Set.range fun n : ℕ => (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ))) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨n, rfl⟩
      rw [div_le_one (by positivity)]
      push_cast; linarith
    refine lt_of_lt_of_le ?_ (le_ciSup hb 0)
    norm_num
  set s := ⨆ n : ℕ, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ))
  let β : ℝ≥0 := ⟨s / 2, by positivity⟩
  have hβ0 : 0 < β := by
    show (0 : ℝ) < s / 2; positivity
  have hβ1 : (β : ℝ) < s := by show s / 2 < s; linarith
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨U, hU, C, hC⟩ := Y_spec.2.2 ω t β hβ0 hβ1
  exact (hC.continuousOn hβ0).continuousAt hU

noncomputable def W (t : ℝ≥0) (ω : Bool × (ℝ≥0 → ℝ)) : ℝ := Y t ω.2 - Y 0 ω.2

noncomputable def P (b : Bool) : Measure (Bool × (ℝ≥0 → ℝ)) :=
  Measure.map (Prod.mk b) gaussianLimit

lemma mk_meas (b : Bool) : Measurable (Prod.mk b : (ℝ≥0 → ℝ) → Bool × (ℝ≥0 → ℝ)) :=
  measurable_prodMk_left

instance (b : Bool) : IsProbabilityMeasure (P b) :=
  Measure.isProbabilityMeasure_map (mk_meas b).aemeasurable

lemma W_meas (t : ℝ≥0) : Measurable (W t) :=
  ((Y_spec.1 t).comp measurable_snd).sub ((Y_spec.1 0).comp measurable_snd)

lemma W_cont (ω : Bool × (ℝ≥0 → ℝ)) : Continuous (fun u => W u ω) :=
  (Y_cont ω.2).sub continuous_const

lemma W_zero (ω : Bool × (ℝ≥0 → ℝ)) : W 0 ω = 0 := by simp [W]

lemma W_brownian (b : Bool) : IsBrownianReal W (P b) := by
  have hX : IsPreBrownianReal (fun t (ω : Bool × (ℝ≥0 → ℝ)) => ω.2 t) (P b) := by
    apply HasLaw.IsPreBrownianReal
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    show Measure.map (fun ω : Bool × (ℝ≥0 → ℝ) => ω.2) (P b) = gaussianLimit
    rw [P, Measure.map_map measurable_snd (mk_meas b)]
    exact Measure.map_id
  refine ⟨hX.congr ?_, ae_of_all _ W_cont⟩
  intro t
  have h1 : ∀ᵐ x ∂gaussianLimit, Y t x = x t ∧ Y 0 x = 0 := by
    have h0 : ∀ᵐ x ∂gaussianLimit, Y 0 x = 0 := by
      filter_upwards [Y_spec.2.1 0, isPreBrownianReal_preBrownian.eval_zero_ae_eq_zero]
        with x hx hx0
      rw [hx]; exact hx0
    filter_upwards [Y_spec.2.1 t, h0] with x hx hx0
    exact ⟨hx, hx0⟩
  have hset : MeasurableSet {ω : Bool × (ℝ≥0 → ℝ) | ω.2 t = W t ω} :=
    measurableSet_eq_fun (measurable_pi_apply t |>.comp measurable_snd) (W_meas t)
  show ∀ᵐ ω ∂(P b), ω.2 t = W t ω
  rw [P, ae_map_iff (mk_meas b).aemeasurable hset]
  filter_upwards [h1] with x hx
  simp [W, hx.1, hx.2]

lemma θ_ae (b : Bool) : ∀ᵐ ω ∂(P b), ω.1 = b := by
  have hset : MeasurableSet {ω : Bool × (ℝ≥0 → ℝ) | ω.1 = b} :=
    measurableSet_eq_fun measurable_fst measurable_const
  rw [P, ae_map_iff (mk_meas b).aemeasurable hset]
  exact ae_of_all _ fun _ => rfl

end PS_t212_aux

open PS_t212_aux PeskirShiryaev.SequentialTesting in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω]
    (P0 P1 : Measure Ω) [IsProbabilityMeasure P0] [IsProbabilityMeasure P1]
    (θ : Ω → Bool) (hθ : Measurable θ)
    (hθ0 : ∀ᵐ ω ∂P0, θ ω = false) (hθ1 : ∀ᵐ ω ∂P1, θ ω = true)
    (W : ℝ≥0 → Ω → ℝ) (hWmeas : ∀ u, Measurable (W u))
    (hWcont : ∀ ω, Continuous (fun u => W u ω)) (hW0 : ∀ ω, W 0 ω = 0)
    (hB0 : IsBrownianReal W P0) (hB1 : IsBrownianReal W P1)
    (μ σ a b T : ℝ) (hμ : μ ≠ 0) (hσ : σ ≠ 0)
    (ha : 0 < a) (hb : 0 < b) (hT : 0 < T),
    let E : Model Ω :=
      { P0 := P0, P1 := P1, prob0 := inferInstance, prob1 := inferInstance,
        θ := θ, θ_measurable := hθ, θ_zero := hθ0, θ_one := hθ1,
        W := W, W_measurable := hWmeas, W_continuous := hWcont, W_zero := hW0,
        brownian0 := hB0, brownian1 := hB1 }
    let C : Parameters :=
      { μ := μ, σ := σ, a := a, b := b, T := T, drift_ne := hμ,
        noise_ne := hσ, a_pos := ha, b_pos := hb, horizon_pos := hT }
    let g := optimalBoundary E C
    ThresholdPair C (lowerThreshold C) (upperThreshold C) ∧
    BoundaryClass C g ∧ SolvesIntegralEquations E C g ∧
    (∀ h : Fin 2 → ℝ → ℝ, BoundaryClass C h →
      SolvesIntegralEquations E C h → ∀ i, EqOn (h i) (g i) (Icc 0 C.T)) ∧
    (∀ p ∈ Icc (0 : ℝ) 1,
      let τ := exitTime E C g 0 p
      Admissible E C C.T τ ∧ stoppingCost E C 0 p τ = value E C 0 p ∧
      ∃ d : Ω → Bool, AdmissibleDecision E C τ d ∧
        PrintedDecision E C g p τ d ∧ bayesRisk E C p τ d = value E C 0 p ∧
        ∀ (s : Ω → ℝ≥0) (e : Ω → Bool), Admissible E C C.T s →
          AdmissibleDecision E C s e → bayesRisk E C p τ d ≤ bayesRisk E C p s e) ∧
    (∀ t ∈ Icc (0 : ℝ) C.T, ∀ i : Fin 2,
      terminalMean E C (g i t) (C.T - t) = gaussianTerminalMean C (g i t) (C.T - t)) ∧
    (∀ t ∈ Icc (0 : ℝ) C.T, ∀ i j : Fin 2, ∀ u ∈ Icc (0 : ℝ) (C.T - t),
      transitionCDF E C (g i t) u (g j (t + u)) =
        gaussianTransitionCDF (C.μ / C.σ) (g i t) u (g j (t + u))) ∧
    (C.a = C.b → ∀ t ∈ Icc (0 : ℝ) C.T, g 1 t = 1 - g 0 t)) := by
  intro H
  have H' := @H (Bool × (ℝ≥0 → ℝ)) _ (P false) (P true) _ _ Prod.fst measurable_fst
    (θ_ae false) (θ_ae true) PS_t212_aux.W W_meas W_cont W_zero
    (W_brownian false) (W_brownian true) 1 1 1 1 1 one_ne_zero one_ne_zero
    one_pos one_pos one_pos
  simp only at H'
  obtain ⟨hTP, hBC, -, -, hp, -⟩ := H'
  set E : Model (Bool × (ℝ≥0 → ℝ)) :=
      { P0 := P false, P1 := P true, prob0 := inferInstance, prob1 := inferInstance,
        θ := Prod.fst, θ_measurable := measurable_fst, θ_zero := θ_ae false,
        θ_one := θ_ae true,
        W := PS_t212_aux.W, W_measurable := W_meas, W_continuous := W_cont,
        W_zero := W_zero, brownian0 := W_brownian false, brownian1 := W_brownian true }
    with hE
  set C : Parameters :=
      { μ := 1, σ := 1, a := 1, b := 1, T := 1, drift_ne := one_ne_zero,
        noise_ne := one_ne_zero, a_pos := one_pos, b_pos := one_pos,
        horizon_pos := one_pos } with hC
  set g := optimalBoundary E C with hg
  have hlow : 0 < lowerThreshold C := hTP.1
  have hcut : 0 < cutoff C := by simp [cutoff, hC]
  obtain ⟨h0a, -, h1a, -⟩ := hBC.2.2.2.1 0 ⟨le_refl _, by simp [hC]⟩
  have hpost : ∀ u ω, posterior E C 0 u ω = 0 := by intro u ω; simp [PeskirShiryaev.SequentialTesting.posterior]
  have hτ : ∀ ω, exitTime E C g 0 0 ω = 0 := by
    intro ω
    have hmem : (0 : ℝ≥0) ∈ {u : ℝ≥0 | (u : ℝ) ≤ C.T - 0 ∧
        posterior E C 0 u ω ∉ Ioo (g 0 (0 + u)) (g 1 (0 + u))} := by
      refine ⟨by simp [hC], ?_⟩
      rw [hpost]
      simp only [NNReal.coe_zero, add_zero, mem_Ioo, not_and, not_lt]
      intro h; linarith
    unfold exitTime
    rw [if_pos ⟨0, hmem⟩]
    exact le_antisymm (csInf_le (OrderBot.bddBelow _) hmem) (zero_le)
  obtain ⟨-, -, d, -, hPD, -⟩ := hp 0 ⟨le_refl _, zero_le_one⟩
  have hprior : prior E 0 = P false := by simp [prior, hE]
  unfold PrintedDecision at hPD
  rw [hprior] at hPD
  have hF : ∀ᵐ ω ∂(P false), False := by
    filter_upwards [hPD] with ω hω
    simp only [hτ, hpost, NNReal.coe_zero] at hω
    rcases hω with ⟨h, -⟩ | ⟨h, -⟩ <;> linarith
  have h := ae_iff.1 hF
  simp only [not_false_eq_true, setOf_true, measure_univ] at h
  exact one_ne_zero h
