-- Prove2me | solution 1 for PI.DegenerateSiegelWeil.Scale.fib_map_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:21:28.99104+00:00
-- url     : https://prove2.me/submissions/38393e46-0380-4a20-ad84-0c88ac7d38e2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_FibMeas0Holds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_IsFibreFamilyReindex
import Theorems.Thm_PI_DegenerateSiegelWeil_Scale_fib_reindex_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DegenerateSiegelWeil PI.DegenerateSiegelWeil.Scale
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal NNReal
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
  [LocallyCompactSpace X]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  [ν.IsOpenPosMeasure]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}
namespace PI.DegenerateSiegelWeil.Scale
theorem _root_.solution (e : V ≃ₜ V) (h : X ≃ₜ X) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (hUo : IsOpen U)
    (heh : ∀ v, f' (e v) = h (f' v)) (hU : e ⁻¹' U = U) {cμ cν : ℝ≥0∞} (hcμ : cμ ≠ ⊤)
    (hcν : cν ≠ ⊤) (hμ : μ.map e = cμ • μ) (hν : ν.map h.symm = cν • ν)
    (hfib : IsFibreFamily μ f ι U ν univ fib) (b : X) (hb : h b = b) :
    (fib b).map e.toMeasurableEquiv = (cμ * cν) • fib b := by
  have hb' : h.symm b = b := h.symm_apply_eq.2 hb.symm
  have := fib_reindex_eq e h hf' hff' hι hUo heh hU hcμ hcν hμ hν hfib b
  rwa [hb'] at this
end PI.DegenerateSiegelWeil.Scale
