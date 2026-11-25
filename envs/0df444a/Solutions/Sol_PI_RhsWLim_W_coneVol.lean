-- Prove2me | solution 1 for PI.RhsWLim.W.coneVol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:03:49.986501+00:00
-- url     : https://prove2.me/submissions/ffbdb3b1-5ed2-469e-bc1f-ac41a2748b20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushM
import Theorems.Thm_PI_RhsWLim_W_lintegral_inv_smul
import Theorems.Thm_PI_RhsWLim_W_polar_symm_exp
import Theorems.Thm_PI_RhsWLim_W_continuous_hq
import Theorems.Thm_PI_RhsWLim_W_measurableSet_coneSh
import Theorems.Thm_PI_RhsWLim_W_radial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
variable {k : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution : ConeVol := by
  intro k T' hT'
  set d := Module.finrank ℝ (Fin k → ℂ) with hd
  set C : ℝ≥0∞ := ∫⁻ t in Set.Ioo (1 : ℝ) 2, ENNReal.ofReal (T' * t) * ENNReal.ofReal (t ^ d) with hC
  refine ⟨C, ?_, ?_, fun E hE => ?_⟩
  · apply ne_of_gt
    calc (0 : ℝ≥0∞) < ENNReal.ofReal T' * volume (Set.Ioo (1 : ℝ) 2) := by
          rw [Real.volume_Ioo]
          exact ENNReal.mul_pos (by simpa using hT') (by norm_num)
      _ = ∫⁻ t in Set.Ioo (1 : ℝ) 2, ENNReal.ofReal T' := (setLIntegral_const _ _).symm
      _ ≤ C := setLIntegral_mono' measurableSet_Ioo fun t ht => by
          have ht1 : 1 < t := ht.1
          rw [← ENNReal.ofReal_mul (by nlinarith)]
          apply ENNReal.ofReal_le_ofReal
          have h1 : 1 ≤ t ^ d := one_le_pow₀ ht1.le
          have h2 : 1 ≤ t * t ^ d := one_le_mul_of_one_le_of_one_le ht1.le h1
          calc T' = T' * 1 := (mul_one _).symm
            _ ≤ T' * (t * t ^ d) := mul_le_mul_of_nonneg_left h2 hT'.le
            _ = T' * t * t ^ d := by ring
  · apply ne_of_lt
    calc C ≤ ∫⁻ t in Set.Ioo (1 : ℝ) 2, ENNReal.ofReal (T' * 2 * 2 ^ d) :=
          setLIntegral_mono' measurableSet_Ioo fun t ht => by
            have ht1 : 1 < t := ht.1
            have ht2 : t < 2 := ht.2
            rw [← ENNReal.ofReal_mul (by nlinarith)]
            apply ENNReal.ofReal_le_ofReal
            have h1 : t ^ d ≤ 2 ^ d := pow_le_pow_left₀ (by linarith) ht2.le d
            have h2 : 0 ≤ t ^ d := pow_nonneg (by linarith) d
            have h3 : T' * t ≤ T' * 2 := by nlinarith
            calc T' * t * t ^ d ≤ T' * 2 * t ^ d := by nlinarith
              _ ≤ T' * 2 * 2 ^ d := by nlinarith
      _ < ⊤ := by
          rw [setLIntegral_const, Real.volume_Ioo]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hS := measurableSet_coneSh hT' hE
  have hf : Measurable (E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞)) := measurable_one.indicator hE
  set F3 : (Fin k → ℂ) → ℝ → ℝ → ℝ≥0∞ := fun y θ t =>
    ENNReal.ofReal (T' * t) * E.indicator 1 (hq k T' (t⁻¹ • y) θ) with hF3
  have hF3m : Measurable (fun p : ((Fin k → ℂ) × ℝ) × ℝ => F3 p.1.1 p.1.2 p.2) := by
    refine (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_snd)).mul ?_
    exact hf.comp ((continuous_hq k T').measurable.comp
      ((measurable_snd.inv.smul (measurable_fst.comp measurable_fst)).prodMk (measurable_snd.comp measurable_fst)))

  have hfib : ∀ y : Fin k → ℂ, volume (Prod.mk y ⁻¹' coneSh k T' E) =
      ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ∫⁻ t in Set.Ioo (1 : ℝ) 2, F3 y θ t := by
    intro y
    have hSy : MeasurableSet (Prod.mk y ⁻¹' coneSh k T' E) := measurable_prodMk_left hS
    have hg : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 •
        (Prod.mk y ⁻¹' coneSh k T' E).indicator (1 : ℂ → ℝ≥0∞) ((p.1 : ℂ) * Complex.exp (p.2 * Complex.I))) := by
      refine (ENNReal.measurable_ofReal.comp measurable_fst).smul ?_
      exact (measurable_one.indicator hSy).comp ((Complex.continuous_ofReal.comp continuous_fst).mul
        (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul
          continuous_const))).measurable
    rw [← lintegral_indicator_one hSy, ← Complex.lintegral_comp_polarCoord_symm]
    simp_rw [polar_symm_exp]
    rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hg.aemeasurable,
      lintegral_lintegral_swap hg.aemeasurable]
    refine lintegral_congr fun θ => ?_
    rw [hF3]
    dsimp only
    rw [← radial hT' E hE y θ]
    refine lintegral_congr fun R => ?_
    rw [smul_eq_mul]
    rfl
  rw [Measure.volume_eq_prod, Measure.prod_apply hS]
  simp_rw [hfib]

  have hm2 : Measurable (fun p : (Fin k → ℂ) × ℝ => ∫⁻ t in Set.Ioo (1 : ℝ) 2, F3 p.1 p.2 t) :=
    hF3m.lintegral_prod_right'
  rw [lintegral_lintegral_swap hm2.aemeasurable]
  have hm3 : ∀ θ : ℝ, Measurable (fun p : (Fin k → ℂ) × ℝ => F3 p.1 θ p.2) := fun θ =>
    hF3m.comp (((measurable_fst).prodMk measurable_const).prodMk measurable_snd)
  have step : ∀ θ : ℝ, ∫⁻ y, ∫⁻ t in Set.Ioo (1 : ℝ) 2, F3 y θ t =
      ∫⁻ t in Set.Ioo (1 : ℝ) 2, ENNReal.ofReal (T' * t) * ENNReal.ofReal (t ^ d) *
        ∫⁻ y, E.indicator 1 (hq k T' y θ) := by
    intro θ
    rw [lintegral_lintegral_swap (hm3 θ).aemeasurable]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have ht0 : 0 < t := by linarith [ht.1]
    rw [hF3]
    dsimp only
    have hGm : Measurable (fun y : Fin k → ℂ => E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' y θ)) :=
      hf.comp ((continuous_hq k T').measurable.comp (measurable_id.prodMk measurable_const))
    rw [lintegral_const_mul (ENNReal.ofReal (T' * t)) (f := fun x => E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞)
      (hq k T' (t⁻¹ • x) θ)) (hGm.comp (measurable_const_smul _))]
    have hsc := lintegral_inv_smul ht0 hGm
    rw [hsc, mul_assoc]
  simp_rw [step]
  have hP : Measurable (fun θ : ℝ => ∫⁻ y, E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' y θ)) := by
    have : Measurable (fun p : (Fin k → ℂ) × ℝ => E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' p.1 p.2)) :=
      hf.comp (continuous_hq k T').measurable
    exact this.lintegral_prod_left'
  have hct : Measurable (fun t : ℝ => ENNReal.ofReal (T' * t) * ENNReal.ofReal (t ^ d)) :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_id)).mul
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const d))
  have hprod : Measurable (Function.uncurry fun (θ : ℝ) (t : ℝ) =>
      ENNReal.ofReal (T' * t) * ENNReal.ofReal (t ^ d) * ∫⁻ y, E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' y θ)) :=
    (hct.comp measurable_snd).mul (hP.comp measurable_fst)
  rw [lintegral_lintegral_swap hprod.aemeasurable]
  unfold hqI
  rw [hC, ← lintegral_mul_const _ hct]
  refine lintegral_congr fun t => ?_
  rw [lintegral_const_mul _ hP]
end PI.RhsWLim.W
