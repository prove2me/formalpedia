-- Prove2me | solution 1 for PositivityTheory.ThKG.Fub.mem_part
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:40:26.746715+00:00
-- url     : https://prove2.me/submissions/13d3c39f-9579-4372-9249-4df27b643b96

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_FubGen
import Mathlib


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
theorem _root_.solution {P : R → G →* G} {K : Subgroup G} {a : R} {g : G} : g ∈ part P K a ↔ g ∈ K ∧ P a g = g := by
  first
    | (intros; rfl)
    | exact Iff.rfl
    | decide
    | (intros; omega)
    | (intros; simp)
    | (intros; simp_all)
    | (intros; norm_num)
    | (intros; positivity)
    | (intros; aesop)
    | (intros; nlinarith)
    | (intros; field_simp; ring)
    | (intros; ext; simp)
    | (intros; constructor <;> intro h <;> simpa using h)
    | (intros; exact?)
  trace "HIT_47_0"

end 
