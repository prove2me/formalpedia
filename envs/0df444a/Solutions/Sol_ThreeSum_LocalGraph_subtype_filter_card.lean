-- Prove2me | solution 1 for ThreeSum.LocalGraph.subtype_filter_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:09:10.149069+00:00
-- url     : https://prove2.me/submissions/d1c2f2f5-de42-47d9-bf14-10f24798bbdf

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Bool.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LocalGraph

set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
open LayerCounts
variable {L h : ℕ}
namespace ThreeSum.LocalGraph
theorem _root_.solution {β : Type*} [DecidableEq β] (s : Finset β)
    (p : β → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun e : s => p e.val)).card = (s.filter p).card := by
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    exact Finset.mem_filter.mpr ⟨e.property, (Finset.mem_filter.mp he).2⟩
  · intro e _ f _ he
    exact Subtype.ext he
  · intro x hx
    refine ⟨⟨x, (Finset.mem_filter.mp hx).1⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
end ThreeSum.LocalGraph
