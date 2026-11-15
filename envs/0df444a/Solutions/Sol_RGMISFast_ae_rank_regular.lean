-- Prove2me | solution 1 for RGMISFast.ae_rank_regular
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-15T01:13:32.44071+00:00
-- url     : https://prove2.me/submissions/3ff7e4c5-6074-4495-afa7-9f8ffd7358b7

import Definitions.Def_RGMISFast_rankLaw
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem solution (V : Type) [Fintype V] :
    ∀ᵐ r ∂(RGMISFast.rankLaw V), Function.Injective r ∧ ∀ v, 0 ≤ r v := by
  classical
  let μ : Measure ℝ := expMeasure 1
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_expMeasure (by norm_num)
  letI : NullSingletonClass μ := by dsimp [μ, expMeasure, gammaMeasure]; infer_instance
  have hmap (v : V) : (RGMISFast.rankLaw V).map (fun r => r v) = μ :=
    (measurePreserving_eval (fun _ : V => μ) v).map_eq
  have hnn : ∀ᵐ x ∂μ, 0 ≤ x := by
    rw [ae_iff]
    simp only [not_le]
    change μ (Set.Iio 0) = 0
    rw [show μ = volume.withDensity (gammaPDF 1 1) from rfl,
      withDensity_apply _ measurableSet_Iio]
    exact lintegral_gammaPDF_of_nonpos le_rfl
  have hall : ∀ᵐ r ∂(RGMISFast.rankLaw V), ∀ v, 0 ≤ r v := by
    apply Filter.eventually_all.mpr
    intro v
    apply ae_of_ae_map (measurable_pi_apply v).aemeasurable
    rw [hmap]
    exact hnn
  have hpair (v w : V) (hvw : v ≠ w) :
      ∀ᵐ r ∂(RGMISFast.rankLaw V), r v ≠ r w := by
    have hind := (iIndepFun_pi (μ := fun _ : V => μ)
      (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hvw
    have hm := hind.map_prod_eq_prod_map_map
      (measurable_pi_apply v).aemeasurable (measurable_pi_apply w).aemeasurable
    change (RGMISFast.rankLaw V).map (fun r => (r v, r w)) =
      ((RGMISFast.rankLaw V).map (fun r => r v)).prod ((RGMISFast.rankLaw V).map (fun r => r w)) at hm
    rw [hmap, hmap] at hm
    have hp : ∀ᵐ z ∂μ.prod μ, z.1 ≠ z.2 := by
      rw [ae_iff]
      simp only [not_not]
      apply Measure.measure_prod_null_of_ae_null
      · exact measurableSet_eq_fun measurable_fst measurable_snd
      · filter_upwards [] with x
        change μ {y : ℝ | x = y} = 0
        simp
    apply ae_of_ae_map (μ := RGMISFast.rankLaw V) (p := fun z : ℝ × ℝ => z.1 ≠ z.2)
      ((measurable_pi_apply v).prodMk (measurable_pi_apply w)).aemeasurable
    rw [hm]
    exact hp
  have hi : ∀ᵐ r ∂(RGMISFast.rankLaw V), Function.Injective r := by
    apply Filter.eventually_all.mpr
    intro v
    apply Filter.eventually_all.mpr
    intro w
    by_cases he : v = w
    · exact Filter.Eventually.of_forall (fun _ _ => he)
    · filter_upwards [hpair v w he] with r hr heq
      exact (hr heq).elim
  exact hi.and hall
