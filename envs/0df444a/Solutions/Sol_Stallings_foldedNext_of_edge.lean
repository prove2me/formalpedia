-- Prove2me | solution 1 for Stallings.foldedNext_of_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:12:55.204368+00:00
-- url     : https://prove2.me/submissions/bab2e613-fbe1-416a-9282-b66be7d93334

import Definitions.Def_Stallings_InverseAutomaton
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Definitions.Def_Stallings_Folding

set_option autoImplicit true
open Stallings
namespace Stallings
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V) {v t : V}
    {x : Letter} (hedge : t ∈ G.edges v x) :
    foldedNext G (foldRep G v) x = some (foldRep G t) := by
  have hcanonical : foldRep G v = foldRep G (foldRep G v) :=
    (foldRep_idem G v).symm
  change (if foldRep G v = foldRep G (foldRep G v) then
    foldedNextCore G (foldRep G v) x else none) = some (foldRep G t)
  rw [if_pos hcanonical]
  have ht : t ∈ foldTargets G (foldRep G v) x := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, v, foldRel.symm G (foldRep_rel G v), hedge⟩
  have hne : (foldTargets G (foldRep G v) x).Nonempty := ⟨t, ht⟩
  unfold foldedNextCore
  rw [dif_pos hne]
  have hmin : (foldTargets G (foldRep G v) x).min' hne ∈
      foldTargets G (foldRep G v) x := Finset.min'_mem _ _
  have hrel := foldTargets_pair G (foldRep G v) x hmin ht
  have hrep := foldRep_eq_of_rel G hrel
  rw [hrep]
end Stallings
