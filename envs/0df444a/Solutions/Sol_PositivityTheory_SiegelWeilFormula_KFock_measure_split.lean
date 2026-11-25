-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFock.measure_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:30.326468+00:00
-- url     : https://prove2.me/submissions/0da11d54-a70d-43c7-8b65-fc32640a8ee3

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_FockSpaces_VolumeIsAddHaar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFock
variable {G H K : Type}
  [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H] [LocallyCompactSpace H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace K] [AddCommGroup K] [IsTopologicalAddGroup K] [LocallyCompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K]
namespace PositivityTheory.SiegelWeilFormula.KFock
theorem _root_.solution (ν : Measure G) [ν.IsAddHaarMeasure] (la : Measure H) [la.IsAddHaarMeasure]
    (mu : Measure K) [mu.IsAddHaarMeasure] (Φ : H × K ≃ₜ+ G) :
    ∃ c : NNReal, 0 < c ∧ ν = c • Measure.map Φ (la.prod mu) := by
  have hmap : (Measure.map Φ (la.prod mu)).IsAddHaarMeasure :=
    Φ.toAddEquiv.isAddHaarMeasure_map (la.prod mu) Φ.continuous Φ.symm.continuous
  refine ⟨Measure.addHaarScalarFactor ν (Measure.map Φ (la.prod mu)),
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _, ?_⟩
  exact Measure.isAddLeftInvariant_eq_smul ν _
end PositivityTheory.SiegelWeilFormula.KFock
