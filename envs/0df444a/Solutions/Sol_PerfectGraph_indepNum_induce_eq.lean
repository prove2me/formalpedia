-- Prove2me | solution 1 for PerfectGraph.indepNum_induce_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:31:28.874105+00:00
-- url     : https://prove2.me/submissions/e960337a-77a5-474f-a091-da44712eaeaa

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
public import Theorems.Thm_PerfectGraph_compl_induce_eq

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)
namespace PerfectGraph
theorem _root_.solution (S : Finset V) :
    (G.induce (S : Set V)).indepNum = (Gᶜ.induce (S : Set V)).cliqueNum := by
  rw [compl_induce_eq, cliqueNum_compl]
end PerfectGraph
