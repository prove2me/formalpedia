-- Prove2me | solution 1 for ThreeSum.LocalGraph.equalityMask_eq_iff_union_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:11:07.321216+00:00
-- url     : https://prove2.me/submissions/8cc176e8-7c37-41e4-8c49-c0d112daca0a

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
import Theorems.Thm_ThreeSum_LocalGraph_equalityMask_eq_union

set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]
namespace ThreeSum.LocalGraph
theorem _root_.solution {s v s' v' : Finset α}
    (hd : Disjoint s v) (hd' : Disjoint s' v') :
    (fun i => leftWord s i == rightWord v i) =
        (fun i => leftWord s' i == rightWord v' i) ↔ s ∪ v = s' ∪ v' := by
  rw [equalityMask_eq_union hd, equalityMask_eq_union hd']
  exact leftWord_injective.eq_iff
end ThreeSum.LocalGraph
