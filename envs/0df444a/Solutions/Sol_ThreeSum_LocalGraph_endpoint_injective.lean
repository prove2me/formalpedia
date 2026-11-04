-- Prove2me | solution 1 for ThreeSum.LocalGraph.endpoint_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:11:09.706217+00:00
-- url     : https://prove2.me/submissions/d1e85e18-fbb0-4dc4-8544-959b490feeb4

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Bool.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Theorems.Thm_ThreeSum_LocalGraph_leftWord_injective
import Theorems.Thm_ThreeSum_LocalGraph_rightWord_injective

set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
open LayerCounts
variable {L h : ℕ}
namespace ThreeSum.LocalGraph
theorem _root_.solution :
    Function.Injective (fun e : Edge L h => (left e, right e)) := by
  intro e f he
  apply Subtype.ext
  exact Prod.ext (leftWord_injective (congrArg Prod.fst he))
    (rightWord_injective (congrArg Prod.snd he))
end ThreeSum.LocalGraph
