-- Prove2me | solution 1 for PositivityTheory.ThKG.Fub.Sys.good_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:46:28.729537+00:00
-- url     : https://prove2.me/submissions/85d6ae35-13bf-40b4-afc8-0392358aff93

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
theorem _root_.solution (s : Sys P K U good) {ι : Type} [DecidableEq ι] (e : ι → R) (he : ∀ i, good (e i))
    (ho : ∀ i j, i ≠ j → e i * e j = 0) (c : R) (hc : good c) (T : Finset ι) (hT : ∀ i ∈ T, e i * c = 0) :
    good (∑ i ∈ T, e i + c) := by
  induction T using Finset.induction_on with
  | empty => simpa using hc
  | insert i T hi ih =>
    rw [Finset.sum_insert hi, add_assoc]
    refine (s.add _ _ (he i) (ih fun j hj => hT j (Finset.mem_insert_of_mem hj)) ?_).1
    rw [mul_add, Finset.mul_sum, Finset.sum_eq_zero fun j hj => ho i j (fun e => hi (e ▸ hj)), hT i (Finset.mem_insert_self _ _),
      add_zero]
end Sys
end PositivityTheory.ThKG.Fub
