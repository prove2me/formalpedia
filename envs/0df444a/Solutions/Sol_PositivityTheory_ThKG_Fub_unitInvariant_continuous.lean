-- Prove2me | solution 1 for PositivityTheory.ThKG.Fub.unitInvariant_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:00:44.00305+00:00
-- url     : https://prove2.me/submissions/fdfe7034-c46a-4116-aa66-2f24347df2ab

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
theorem _root_.solution {A : Type} [Ring A] [Algebra R A] [TopologicalSpace A] [IsTopologicalRing A] [ContinuousConstSMul R A] {a : R}
    (h : a * a = a) : Continuous (unitP (A := A) a) := by
  unfold unitP; rw [dif_pos h]
  exact Continuous.units_map _ (by show Continuous fun x : A => a • x + (1 - a) • (1 : A); fun_prop)
end PositivityTheory.ThKG.Fub
