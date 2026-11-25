-- Prove2me | solution 1 for PositivityTheory.ThKG.Fub.unitInvariant_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:00:42.04104+00:00
-- url     : https://prove2.me/submissions/af1a1466-2436-401f-a6ce-d19c4ae62203

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_FubGen
import Theorems.Thm_PositivityTheory_ThKG_Fub_coe_unitP

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
theorem _root_.solution {A : Type} [Ring A] [Algebra R A] {a b : R} (ha : a * a = a) (hb : b * b = b) (x : Aˣ) :
    unitP a (unitP b x) = unitP (a * b) x := by
  have : a * b * (a * b) = a * b := by rw [mul_mul_mul_comm, ha, hb]
  ext; rw [coe_unitP ha, coe_unitP hb, coe_unitP this]; module
end PositivityTheory.ThKG.Fub
