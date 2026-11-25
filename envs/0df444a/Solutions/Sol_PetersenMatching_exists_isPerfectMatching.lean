-- Prove2me | solution 1 for PetersenMatching.exists_isPerfectMatching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:49:23.452786+00:00
-- url     : https://prove2.me/submissions/8213163e-9c4c-4778-869a-dd188dfb6f7b

module
public import Mathlib
public import Definitions.Def_PetersenLib_Petersen
public import Definitions.Def_PetersenMatching_Solution
public import Theorems.Thm_PetersenTheorem_exists_isPerfectMatching


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PetersenMatching
variable {V : Type*}
namespace PetersenMatching
theorem _root_.solution [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ M : G.Subgraph, M.IsPerfectMatching :=
  PetersenTheorem.exists_isPerfectMatching G h3 hb
end PetersenMatching
