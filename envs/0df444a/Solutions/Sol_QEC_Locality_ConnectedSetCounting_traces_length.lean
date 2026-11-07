-- Prove2me | solution 1 for QEC.Locality.ConnectedSetCounting.traces_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:52:20.740677+00:00
-- url     : https://prove2.me/submissions/8d0d902c-2531-43e5-8b96-944fddb7fc2b

import Definitions.Def_QEC_Locality_Graph_Core
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
section
noncomputable section
namespace QEC.Locality.ConnectedSetCounting
open Classical
open scoped BigOperators
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
private theorem mem_traces_succ (G : SimpleGraph V) (r : V) (n : Nat) (l : List V) :
    l ∈ traces G r (n+1) ↔
      ∃ w ∈ next G r, ∃ t ∈ traces G w n, r::t = l := by
  classical
  simp only [traces, Finset.mem_biUnion, Finset.mem_image]
end QEC.Locality.ConnectedSetCounting
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.ConnectedSetCounting
open Classical
open scoped BigOperators
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.ConnectedSetCounting
theorem _root_.solution (G : SimpleGraph V) (r : V) (n : Nat) (l : List V)
    (hl : l ∈ traces G r n) : l.length = n+1 := by
  induction n generalizing r l with
  | zero =>
    have he : l = [r] := by simpa [traces] using hl
    simp [he]
  | succ n ih =>
    obtain ⟨w,hw,t,ht,rfl⟩ := (mem_traces_succ G r n l).mp hl
    simpa only [List.length_cons] using congrArg Nat.succ (ih w t ht)
end QEC.Locality.ConnectedSetCounting
