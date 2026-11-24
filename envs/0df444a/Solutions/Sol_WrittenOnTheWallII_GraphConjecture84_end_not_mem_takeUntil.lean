-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.end_not_mem_takeUntil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:33:47.117833+00:00
-- url     : https://prove2.me/submissions/4321afe5-d494-461d-84b1-90ba1cb99122

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
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} {u v z : α} (p : G.Walk u v)
    (hp : p.IsPath) (hz : z ∈ p.support) (hzv : z ≠ v) :
    v ∉ (p.takeUntil z hz).support := by
  intro hv
  have hpath : ((p.takeUntil z hz).append (p.dropUntil z hz)).IsPath := by
    rw [p.take_spec hz]
    exact hp
  exact hpath.ne_of_mem_support_of_append hzv.symm hv (p.dropUntil z hz).end_mem_support rfl
end WrittenOnTheWallII.GraphConjecture84
