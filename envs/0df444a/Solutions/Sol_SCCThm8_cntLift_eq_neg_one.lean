-- Prove2me | solution 1 for SCCThm8.cntLift_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:55:05.806678+00:00
-- url     : https://prove2.me/submissions/c794bdce-85f8-4c0a-85d7-5de872b41b9f

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution {n : ℕ} {v : Finset (Fin n)} {i : Fin n} (h : cntLift v i = -1) :
    i ∈ v ∧ ¬ 2 * cntRank v i < v.card := by
  unfold cntLift at h
  split_ifs at h with h1 h2
  exact ⟨h1, h2⟩
end SCCThm8
