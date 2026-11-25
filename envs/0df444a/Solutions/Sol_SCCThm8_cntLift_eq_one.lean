-- Prove2me | solution 1 for SCCThm8.cntLift_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:59.373041+00:00
-- url     : https://prove2.me/submissions/361dce2a-13f1-46be-a69e-4f736251e2a8

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution {n : ℕ} {v : Finset (Fin n)} {i : Fin n} (h : cntLift v i = 1) :
    i ∈ v ∧ 2 * cntRank v i < v.card := by
  unfold cntLift at h
  split_ifs at h with h1 h2 <;> simp_all
end SCCThm8
