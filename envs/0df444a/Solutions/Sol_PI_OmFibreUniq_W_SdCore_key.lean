-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdCore.key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:24.228825+00:00
-- url     : https://prove2.me/submissions/f0506ef9-7142-4db2-b010-55e5dd18db19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExCore
import Theorems.Thm_PI_OmFibreUniq_W_SdCore_isClosed_ann
import Theorems.Thm_PI_VolStabSW_SdUniqW_transform_indicator


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.SdCore
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter
open PI.VolStabSW.SdUniqW
open scoped ENNReal
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
variable (χ : V → V → ℂ) (hχc : Continuous (fun p : V × V => χ p.1 p.2))
  (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (hsym : ∀ x y, χ x y = χ y x)
  (hn : ∀ x y, ‖χ x y‖ = 1)
  (μ : Measure V) [μ.IsAddHaarMeasure] (M : AddSubgroup V) (hMc : IsCompact (M : Set V))
  (hMo : IsOpen (M : Set V))
include hχc hχ hsym hn hMc hMo
namespace PI.OmFibreUniq.W.SdCore
theorem _root_.solution (Φ : V → ℂ) (hc : Continuous Φ) (hs : HasCompactSupport Φ) (z : V) :
    ∫ y in (M : Set V), (∫ x, Φ x * χ x y ∂μ) * χ y z ∂μ =
      (μ.real (M : Set V) : ℂ) * ∫ u in ann χ M, Φ (u - z) ∂μ := by
  have hΦi : Integrable Φ μ := hc.integrable_of_hasCompactSupport hs
  have hm : MeasurableSet (M : Set V) := hMo.measurableSet
  have h1 : ∀ y, (∫ x, Φ x * χ x y ∂μ) * χ y z = ∫ x, Φ x * χ (x + z) y ∂μ := by
    intro y
    rw [← integral_mul_const]
    congr 1
    funext x
    rw [hχ z x y, hsym z y, mul_assoc]
  simp only [h1]
  haveI : IsFiniteMeasure (μ.restrict (M : Set V)) :=
    isFiniteMeasure_restrict.2 hMc.measure_lt_top.ne
  have hint : Integrable (Function.uncurry fun (y x : V) => Φ x * χ (x + z) y)
      ((μ.restrict (M : Set V)).prod μ) := by
    have hb : Integrable (fun p : V × V => (1 : ℝ) * ‖Φ p.2‖) ((μ.restrict (M : Set V)).prod μ) :=
      Integrable.mul_prod (integrable_const (1 : ℝ)) hΦi.norm
    refine hb.mono' ?_ ?_
    · have hcont : Continuous (Function.uncurry fun (y x : V) => Φ x * χ (x + z) y) := by
        show Continuous fun p : V × V => Φ p.2 * χ (p.2 + z) p.1
        exact (hc.comp continuous_snd).mul
          (hχc.comp ((continuous_snd.add continuous_const).prodMk continuous_fst))
      exact hcont.aestronglyMeasurable
    · filter_upwards with p
      simp [Function.uncurry, norm_mul, hn]
  rw [integral_integral_swap hint]
  have h2 : ∀ x, ∫ y in (M : Set V), Φ x * χ (x + z) y ∂μ =
      (ann χ M).indicator (fun _ => (μ.real (M : Set V) : ℂ)) (x + z) * Φ x := by
    intro x
    rw [integral_const_mul, ← transform_indicator μ χ hχ M hMo (x + z), ← integral_indicator hm,
      mul_comm]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    by_cases hy : y ∈ (M : Set V)
    · simp [Set.indicator_of_mem hy, hsym]
    · simp [Set.indicator_of_notMem hy]
  simp only [h2]
  have h3 : ∀ x, (ann χ M).indicator (fun _ => (μ.real (M : Set V) : ℂ)) (x + z) * Φ x =
      (μ.real (M : Set V) : ℂ) * (ann χ M).indicator (fun u => Φ (u - z)) (x + z) := by
    intro x
    by_cases hx : x + z ∈ ann χ M
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  simp only [h3]
  rw [integral_const_mul,
    integral_add_right_eq_self (fun w => (ann χ M).indicator (fun u => Φ (u - z)) w) z,
    integral_indicator (isClosed_ann χ hχc M).measurableSet]
end PI.OmFibreUniq.W.SdCore
