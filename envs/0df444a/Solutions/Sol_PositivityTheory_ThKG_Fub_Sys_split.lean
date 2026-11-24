-- Prove2me | solution 1 for PositivityTheory.ThKG.Fub.Sys.split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:46:29.695062+00:00
-- url     : https://prove2.me/submissions/d0b7d743-bfc5-4520-96df-87b7e863f460

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_FubGen
import Theorems.Thm_PositivityTheory_ThKG_Fub_Sys_closed

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
theorem _root_.solution (s : Sys P K U good) {a b : R} (ha : good a) (hb : good b) (hab : a * b = 0) :
    Split (part P K (a + b)) (part P K a) (part P K b) (P a) (P b) where
  cp := s.cont a ha
  cq := s.cont b hb
  cA := s.closed ha
  cB := s.closed hb
  cS := s.closed (s.add a b ha hb hab).1
  mA g hg := ⟨s.mK a ha g hg.1, by show P a (P a g) = P a g; rw [s.comp a a ha ha, s.idem a ha]⟩
  mB g hg := ⟨s.mK b hb g hg.1, by show P b (P b g) = P b g; rw [s.comp b b hb hb, s.idem b hb]⟩
  mul g hg := ((s.add a b ha hb hab).2 g).symm.trans hg.2
  hA g hg := by
    have h0 : P a g = g := hg.2
    have h1 : P b g = 1 := by rw [← h0, s.comp b a hb ha, mul_comm, hab, s.zero]
    exact ⟨⟨hg.1, by show P (a + b) g = g; rw [(s.add a b ha hb hab).2, h0, h1, mul_one]⟩, h0, h1⟩
  hB g hg := by
    have h0 : P b g = g := hg.2
    have h1 : P a g = 1 := by rw [← h0, s.comp a b ha hb, hab, s.zero]
    exact ⟨⟨hg.1, by show P (a + b) g = g; rw [(s.add a b ha hb hab).2, h0, h1, one_mul]⟩, h0, h1⟩
end Sys
end PositivityTheory.ThKG.Fub
