-- Prove2me | solution 1 for PerfectGraph.chromaticNumber_eq_iff_isColOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:34:45.116282+00:00
-- url     : https://prove2.me/submissions/c5384bf5-b016-4ce1-86b6-c4fccfa174ac

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
public import Theorems.Thm_PerfectGraph_colorable_induce_iff

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)
namespace PerfectGraph
theorem _root_.solution (S : Finset V) :
    (G.induce (S : Set V)).chromaticNumber = (G.induce (S : Set V)).cliqueNum ↔
      IsColOn G S (G.induce (S : Set V)).cliqueNum := by
  rw [← colorable_induce_iff, ← chromaticNumber_le_iff_colorable]
  exact ⟨fun h => h.le, fun h => le_antisymm h cliqueNum_le_chromaticNumber⟩
end PerfectGraph
