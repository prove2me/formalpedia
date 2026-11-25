-- Prove2me | solution 1 for PetersenMatching.exists_isPerfectMatching_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:49:26.229808+00:00
-- url     : https://prove2.me/submissions/13aece67-0acd-46c9-a999-686a86ef1713

module
public import Mathlib
public import Definitions.Def_PetersenLib_Petersen
public import Definitions.Def_PetersenMatching_Solution
public import Theorems.Thm_PetersenTheorem_exists_isPerfectMatching_mem


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PetersenMatching
variable {V : Type*}
namespace PetersenMatching
theorem _root_.solution [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∀ e ∈ G.edgeSet, ∃ M : G.Subgraph, M.IsPerfectMatching ∧ e ∈ M.edgeSet :=
  PetersenTheorem.exists_isPerfectMatching_mem G h3 hb
end PetersenMatching
