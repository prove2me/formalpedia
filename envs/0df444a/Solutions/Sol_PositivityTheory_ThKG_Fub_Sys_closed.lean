-- Prove2me | solution 1 for PositivityTheory.ThKG.Fub.Sys.closed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:43.719005+00:00
-- url     : https://prove2.me/submissions/251adef1-fad6-475b-8b4f-8f781e581004

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
variable {R : Type} [CommRing R]
variable {P : R → G →* G} {K : Subgroup G} {U : Set G} {good : R → Prop}
namespace PositivityTheory.ThKG.Fub
namespace Sys
theorem _root_.solution (s : Sys P K U good) {a : R} (ha : good a) : IsClosed (part P K a : Set G) :=
  s.cK.inter (isClosed_eq (s.cont a ha) continuous_id)
end Sys
end PositivityTheory.ThKG.Fub
