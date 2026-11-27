-- Prove2me | solution 2 for PositivityTheory.ThKG.Fub.mem_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:24:53.083503+00:00
-- url     : https://prove2.me/submissions/f236997b-657b-460c-b18b-23b3c6535b5c

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
namespace PositivityTheory.ThKG.Fub
theorem _root_.solution {P : R → G →* G} {K : Subgroup G} {a : R} {g : G} : g ∈ part P K a ↔ g ∈ K ∧ P a g = g := Iff.rfl
end PositivityTheory.ThKG.Fub
