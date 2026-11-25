-- Prove2me | solution 1 for SimpleGraph.card_filter_toFinset_of_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:43:26.425696+00:00
-- url     : https://prove2.me/submissions/d59b17a5-d4c5-4a0d-8246-b44c987bd693

module
public import Definitions.Def_Euler_Trail
public import Definitions.Def_Euler_Orientation

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    (p : α → Prop) [DecidablePred p] : (l.toFinset.filter p).card = l.countP p := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hl.filter _)]
  congr 1
  ext a
  simp
end SimpleGraph
