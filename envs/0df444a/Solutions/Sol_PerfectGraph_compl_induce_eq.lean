-- Prove2me | solution 1 for PerfectGraph.compl_induce_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:27:57.550683+00:00
-- url     : https://prove2.me/submissions/1e9fbc12-319c-428c-821e-69051cbfbf85

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)
namespace PerfectGraph
theorem _root_.solution (S : Set V) : Gᶜ.induce S = (G.induce S)ᶜ := by
  ext x y
  simp [Subtype.coe_injective.ne_iff]
end PerfectGraph
