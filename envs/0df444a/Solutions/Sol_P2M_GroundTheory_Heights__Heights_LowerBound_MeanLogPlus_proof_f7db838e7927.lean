-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBound_MeanLogPlus_proof_f7db838e7927
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:08:18.683989+00:00
-- url     : https://prove2.me/submissions/1397650b-006f-4f0c-8cd9-4c7a18f3ab3d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PMeanLogPlus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBound_lt_max_zero_log_div_iff_c2c029cf849b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBound_log_two_mul_pow_div_add_le_751b1dc9fd76

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBound
open Real MeasureTheory Filter Topology Set
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.LowerBound
namespace MeanLogPlus
theorem _root_.solution (h1 : TailBound.Statement.{u}) : MeanLogPlus.Statement.{u} := by
  intro X _ μ lam cnt a ka r h
  have := h.isProbability
  have hk0 : 0 < ka := by
    have : (1 : ℝ) ≤ a := by exact_mod_cast h.one_le_a
    linarith [h.three_a_le_ka]
  set F : X → ℝ := fun z => max 0 (log (r / lam z)) with hF
  have hFm : Measurable F :=
    measurable_const.max (measurable_log.comp (measurable_const.div h.lam_meas))
  have hF0 : ∀ z, 0 ≤ F z := fun z => le_max_left _ _
  set C : ℝ := 2 * 36 ^ a with hC
  have hC1 : 1 ≤ C := by rw [hC]; have : (1 : ℝ) ≤ 36 ^ a := one_le_pow₀ (by norm_num); linarith
  set x0 : ℝ := log C / ka with hx0
  have hx00 : 0 ≤ x0 := div_nonneg (log_nonneg hC1) hk0.le
  set g : ℝ → ℝ := fun t => min 1 (C * exp (-ka * t)) with hg

  have hpt : ∀ t ∈ Ioi (0 : ℝ), μ {z | t < F z} ≤ ENNReal.ofReal (g t) := by
    intro t ht
    have hset : {z | t < F z} = {z | lam z < exp (-t) * r} := by
      ext z; exact lt_max_zero_log_div_iff ht h.r_pos (h.lam_pos z)
    rw [hset, ← ofReal_measureReal]
    apply ENNReal.ofReal_le_ofReal
    have := h1 X μ lam cnt a ka r h t (le_of_lt ht)
    simpa [hg, neg_mul] using this

  have hexp : IntegrableOn (fun t => C * exp (-ka * t)) (Ioi x0) :=
    (exp_neg_integrableOn_Ioi x0 hk0).const_mul C
  have hint : ∫ t in Ioi x0, C * exp (-ka * t) = 1 / ka := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) x0]
    have : exp (-ka * x0) = C⁻¹ := by
      rw [hx0, show -ka * (log C / ka) = -log C by field_simp, exp_neg,
        exp_log (by linarith)]
    rw [this]; field_simp
  have hL : ∫⁻ z, ENNReal.ofReal (F z) ∂μ ≤ ENNReal.ofReal 3 := by
    rw [lintegral_eq_lintegral_meas_lt μ (ae_of_all _ hF0) hFm.aemeasurable]
    calc ∫⁻ t in Ioi 0, μ {z | t < F z}
        ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (g t) := setLIntegral_mono' measurableSet_Ioi hpt
      _ ≤ ∫⁻ t in Ioc 0 x0 ∪ Ioi x0, ENNReal.ofReal (g t) := by
          rw [Ioc_union_Ioi_eq_Ioi hx00]
      _ ≤ (∫⁻ t in Ioc 0 x0, ENNReal.ofReal (g t)) + ∫⁻ t in Ioi x0, ENNReal.ofReal (g t) :=
          lintegral_union_le _ _ _
      _ ≤ (∫⁻ t in Ioc 0 x0, 1) + ∫⁻ t in Ioi x0, ENNReal.ofReal (C * exp (-ka * t)) :=
          add_le_add (lintegral_mono fun t => ENNReal.ofReal_le_one.2 (min_le_left _ _))
            (lintegral_mono fun t => ENNReal.ofReal_le_ofReal (min_le_right _ _))
      _ = ENNReal.ofReal x0 + ENNReal.ofReal (1 / ka) := by
          rw [setLIntegral_const, one_mul, Real.volume_Ioc, sub_zero, ← hint,
            ofReal_integral_eq_lintegral_ofReal hexp
              (ae_of_all _ fun t => by positivity)]
      _ = ENNReal.ofReal (x0 + 1 / ka) := (ENNReal.ofReal_add hx00 (by positivity)).symm
      _ ≤ ENNReal.ofReal 3 :=
          ENNReal.ofReal_le_ofReal (log_two_mul_pow_div_add_le h.one_le_a h.three_a_le_ka)
  have hInt : Integrable F μ := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hF0)]
    exact lt_of_le_of_lt hL ENNReal.ofReal_lt_top
  refine ⟨hInt, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hF0) hFm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hL
end MeanLogPlus
end GroundTheory.Heights₂.Heights.LowerBound
