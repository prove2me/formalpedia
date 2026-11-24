-- Prove2me | solution 1 for PositivityTheory.ThKG.Fub.exists_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:46:30.724801+00:00
-- url     : https://prove2.me/submissions/02e17cc9-f434-4dc4-916a-fcb5ae53f824

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_FubGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Fub
open MeasureTheory Topology Filter
open scoped NNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable {S A B : Subgroup G} {p q : G →* G}
namespace PositivityTheory.ThKG.Fub
theorem _root_.solution (S : Subgroup G) (hS : IsClosed (S : Set G)) (U : Set G) (h1 : (1 : G) ∈ U)
    (hc : IsCompact {x : S | x.1 ∈ U}) (ho : IsOpen {x : S | x.1 ∈ U}) :
    ∃ μ : Measure S, μ.IsHaarMeasure ∧ μ {x | x.1 ∈ U} = 1 := by
  haveI : LocallyCompactSpace S := hS.locallyCompactSpace
  let K : TopologicalSpace.PositiveCompacts S := ⟨⟨_, hc⟩, ⟨1, by simpa [ho.interior_eq] using h1⟩⟩
  exact ⟨Measure.haarMeasure K, inferInstance, Measure.haarMeasure_self⟩
end PositivityTheory.ThKG.Fub
