-- Prove2me | solution 1 for PI.VolStabSW.DensGen.eq_zero_of_setIntegral_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:50:28.168924+00:00
-- url     : https://prove2.me/submissions/0f7963f2-71e6-4cc4-a117-ba6417d4d89d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensGen
import Theorems.Thm_PI_VolStabSW_DensGen_eq_zero_of_setIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.DensGen
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {B : Set X}
  {fib : X → Measure V}
namespace PI.VolStabSW.DensGen
theorem _root_.solution [LocallyCompactSpace X] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] (D : X → ℂ) (W : Set X) (b0 : X) (hW : W ∈ 𝓝 b0)
    (hD : ContinuousOn D W) (h0 : ∀ S, IsCompact S → S ⊆ W → ∫ b in S, D b ∂ν = 0) :
    D b0 = 0 := by
  have hre : (D b0).re = 0 := by
    refine eq_zero_of_setIntegral (ν := ν) (fun b => (D b).re) W b0 hW
      (Complex.continuous_re.comp_continuousOn hD) (fun S hS hSW => ?_)
    have hint : IntegrableOn D S ν := (hD.mono hSW).integrableOn_compact hS
    have h1 := integral_re hint
    simp only [RCLike.re_to_complex] at h1
    rw [h1, h0 S hS hSW, Complex.zero_re]
  have him : (D b0).im = 0 := by
    refine eq_zero_of_setIntegral (ν := ν) (fun b => (D b).im) W b0 hW
      (Complex.continuous_im.comp_continuousOn hD) (fun S hS hSW => ?_)
    have hint : IntegrableOn D S ν := (hD.mono hSW).integrableOn_compact hS
    have h1 := integral_im hint
    simp only [RCLike.im_to_complex] at h1
    rw [h1, h0 S hS hSW, Complex.zero_im]
  exact Complex.ext hre him
end PI.VolStabSW.DensGen
