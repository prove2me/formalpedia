-- Prove2me | solution 1 for PI.VolStabW.DensGen.fib_set_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:55:47.908783+00:00
-- url     : https://prove2.me/submissions/ee344254-b73a-40f1-ad01-18f02b62e5c9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensGen
import Theorems.Thm_PI_VolStabW_DensGen_ae_fib

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.DensGen
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {B : Set X}
  {fib : X → Measure V}
namespace PI.VolStabW.DensGen
theorem _root_.solution [IsFiniteMeasureOnCompacts ν]
    (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (ρ : V → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (hρ0 : ∀ v, 0 ≤ ρ v) (S : Set X) (hS : IsCompact S) (hSB : S ⊆ B) :
    ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hAm : MeasurableSet (f' ⁻¹' S) := (hS.isClosed.preimage hf').measurableSet
  have h3 := hfib.2.2 ρ hρc hρs hρU
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hρ0) hρc.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun b => integral_nonneg fun v => hρ0 v)
      ((h3.2.mono hSB).aestronglyMeasurable hSm)]
  congr 1
  have hmeas : Measurable fun v => ENNReal.ofReal (ρ v) := hρc.measurable.ennreal_ofReal
  have hsupp : ((f' ⁻¹' S).indicator (fun v => ENNReal.ofReal (ρ v))).support ⊆ U := by
    intro v hv
    apply hρU
    apply subset_tsupport
    intro h0
    apply hv
    simp [h0]
  calc ∫⁻ v in f' ⁻¹' S, ENNReal.ofReal (ρ v) ∂μ
      = ∫⁻ v in U, (f' ⁻¹' S).indicator (fun v => ENNReal.ofReal (ρ v)) v ∂μ := by
        rw [setLIntegral_eq_of_support_subset hsupp, lintegral_indicator hAm]
    _ = ∫⁻ b, ∫⁻ v, (f' ⁻¹' S).indicator (fun v => ENNReal.ofReal (ρ v)) v ∂(fib b) ∂ν :=
        hfib.2.1 _ (hmeas.indicator hAm)
    _ = ∫⁻ b, S.indicator (fun b => ∫⁻ v, ENNReal.ofReal (ρ v) ∂(fib b)) b ∂ν := by
        refine lintegral_congr fun b => ?_
        by_cases hb : b ∈ S
        · rw [Set.indicator_of_mem hb]
          refine lintegral_congr_ae ?_
          filter_upwards [ae_fib hfib hff' hι b] with v hv
          have hv' : v ∈ f' ⁻¹' S := by simp [hv, hb]
          simp [Set.indicator_of_mem hv']
        · have e0 : S.indicator (fun b => ∫⁻ v, ENNReal.ofReal (ρ v) ∂(fib b)) b = 0 := by
            simp [hb]
          rw [e0]
          have : (fun v => (f' ⁻¹' S).indicator (fun v => ENNReal.ofReal (ρ v)) v)
              =ᵐ[fib b] fun _ => 0 := by
            filter_upwards [ae_fib hfib hff' hι b] with v hv
            have hv' : v ∉ f' ⁻¹' S := by simp [hv, hb]
            simp [hv']
          rw [lintegral_congr_ae this, lintegral_zero]
    _ = ∫⁻ b in S, ∫⁻ v, ENNReal.ofReal (ρ v) ∂(fib b) ∂ν := lintegral_indicator hSm _
    _ = ∫⁻ b in S, ENNReal.ofReal (∫ v, ρ v ∂(fib b)) ∂ν := by
        refine setLIntegral_congr_fun hSm ?_
        intro b hb
        exact (ofReal_integral_eq_lintegral_ofReal (h3.1 b (hSB hb))
          (Eventually.of_forall hρ0)).symm
end PI.VolStabW.DensGen
