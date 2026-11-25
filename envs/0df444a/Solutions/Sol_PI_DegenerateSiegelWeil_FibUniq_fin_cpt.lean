-- Prove2me | solution 1 for PI.DegenerateSiegelWeil.FibUniq.fin_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:34:49.989742+00:00
-- url     : https://prove2.me/submissions/f0b8314f-6ec6-4982-bd8d-28a94f9f775f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolSemiDirect
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_HformSmulRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibDis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_FibMeas0Holds

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
theorem _root_.solution {fib : X → Measure V} (h : IsFibreFamily μ f ι U ν univ fib) (hU : IsOpen U)
    (b : X) (K : Set V) (hK : IsCompact K) (hKU : K ⊆ U) : fib b K < ⊤ := by
  obtain ⟨g, hgK, hgc, hgU, -⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  have hi := (h.2.2 g g.continuous hgc hgU).1 b (mem_univ b)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  calc fib b K = ∫⁻ v, K.indicator 1 v ∂fib b := (lintegral_indicator_one hKm).symm
    _ ≤ ∫⁻ v, ENNReal.ofReal (g v) ∂fib b := lintegral_mono fun v => by
        by_cases hv : v ∈ K
        · simp [hv, hgK hv]
        · simp [hv]
    _ < ⊤ := hi.lintegral_lt_top
end PI.DegenerateSiegelWeil.FibUniq
