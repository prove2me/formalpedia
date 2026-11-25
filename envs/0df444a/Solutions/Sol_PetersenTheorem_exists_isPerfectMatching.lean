-- Prove2me | solution 1 for PetersenTheorem.exists_isPerfectMatching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:39:07.776657+00:00
-- url     : https://prove2.me/submissions/db73032a-6a1c-484e-80a7-32fbc23af303

module
public import Mathlib
public import Definitions.Def_PetersenLib_Petersen
public import Theorems.Thm_PetersenTheorem_three_mul_oddComponents_le
public import Theorems.Thm_PetersenTheorem_sum_card_neighborFinset_sdiff_le

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PetersenTheorem
variable {V : Type*}
namespace PetersenTheorem
theorem _root_.solution [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  rw [tutte]
  intro S hS
  rw [IsTutteViolator] at hS
  have h := three_mul_oddComponents_le G h3 hb G S (Function.Embedding.refl V) S.toFinset
    (fun w hw => by simpa using hw)
    (fun w hw y hadj hy => ⟨y, rfl, hadj, by simpa using hy⟩)
  have h' := sum_card_neighborFinset_sdiff_le G h3 S.toFinset
  rw [← Set.ncard_eq_toFinset_card'] at h'
  omega
end PetersenTheorem
