-- Prove2me | solution 1 for PI.DegenerateSiegelWeil.FibUniq.integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:15.450676+00:00
-- url     : https://prove2.me/submissions/1f39f0d5-0e6d-452e-b6a4-eaad4dc7871d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolSemiDirect
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_HformSmulRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibDis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_FibMeas0Holds
import Theorems.Thm_PI_VolStabSW_DensGen_eq_zero_of_setIntegral
import Theorems.Thm_PI_VolStabSW_DensGen_fib_set


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DegenerateSiegelWeil PI.DegenerateSiegelWeil.FibUniq
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  [ν.IsOpenPosMeasure]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib1 fib2 : X → Measure V}
namespace PI.DegenerateSiegelWeil.FibUniq
theorem _root_.solution (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (φ : V → ℝ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (b : X) :
    ∫ v, φ v ∂(fib1 b) = ∫ v, φ v ∂(fib2 b) := by
  have c1 := (h1.2.2 φ hφc hφs hφU).2
  have c2 := (h2.2.2 φ hφc hφs hφU).2
  have h0 : ∀ S, IsCompact S → S ⊆ univ →
      ∫ b in S, (∫ v, φ v ∂(fib1 b) - ∫ v, φ v ∂(fib2 b)) ∂ν = 0 := by
    intro S hS _
    rw [integral_sub ((c1.mono (subset_univ S)).integrableOn_compact hS)
      ((c2.mono (subset_univ S)).integrableOn_compact hS),
      ← PI.VolStabSW.DensGen.fib_set h1 hf' hff' hι φ hφc hφs hφU S hS (subset_univ S),
      ← PI.VolStabSW.DensGen.fib_set h2 hf' hff' hι φ hφc hφs hφU S hS (subset_univ S), sub_self]
  exact sub_eq_zero.1 (PI.VolStabSW.DensGen.eq_zero_of_setIntegral (ν := ν)
    (fun b => ∫ v, φ v ∂(fib1 b) - ∫ v, φ v ∂(fib2 b)) univ b univ_mem (c1.sub c2) h0)
end PI.DegenerateSiegelWeil.FibUniq
