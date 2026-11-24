-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.length_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:25:09.541649+00:00
-- url     : https://prove2.me/submissions/4ed3bbe4-8178-4183-a295-359cf67b5ea5

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
open WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
variable {G : SimpleGraph α} {K : Finset α} (F : PendantGeodesics G K)
namespace WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
theorem _root_.solution (hG : G.Connected) (c : ↥(K : Set α)) :
    0 < (F.path c).length ↔ F.endPoint c ≠ (c : α) := by
  rw [F.geodesic c]
  constructor
  · intro h heq
    simp [heq] at h
  · intro h
    have hne : G.dist (c : α) (F.endPoint c) ≠ 0 :=
      fun hz => h (hG.dist_eq_zero_iff.mp hz).symm
    omega
end WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
