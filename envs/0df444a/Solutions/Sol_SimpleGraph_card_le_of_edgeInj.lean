-- Prove2me | solution 1 for SimpleGraph.card_le_of_edgeInj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:43:38.25447+00:00
-- url     : https://prove2.me/submissions/e77939c1-1620-420a-89cd-a121132228f7

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
theorem _root_.solution {Ds : Finset G.Dart} (hinj : EdgeInj Ds) :
    Ds.card ≤ G.edgeFinset.card := by
  rw [← card_image_of_injOn fun d hd d' hd' h => hinj d hd d' hd' h]
  refine card_le_card fun e he => ?_
  obtain ⟨d, -, rfl⟩ := mem_image.mp he
  rw [mem_edgeFinset]
  exact d.edge_mem
end SimpleGraph
