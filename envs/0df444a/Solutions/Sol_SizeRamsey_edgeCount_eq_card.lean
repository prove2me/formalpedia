-- Prove2me | solution 1 for SizeRamsey.edgeCount_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:18:09.500784+00:00
-- url     : https://prove2.me/submissions/943ec3be-9208-4616-8a01-c026b557948d

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
namespace SizeRamsey
theorem _root_.solution {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet] :
    edgeCount G = G.edgeFinset.card := by
  unfold edgeCount
  congr 1
  ext e
  simp only [SimpleGraph.mem_edgeFinset]
end SizeRamsey
