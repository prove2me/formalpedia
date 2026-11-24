-- Prove2me | solution 1 for ULHC.sidesIn_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:54:39.741838+00:00
-- url     : https://prove2.me/submissions/ab93b93d-9da2-4482-8fb0-ba5c6d16aa52

import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_Reroute
import Theorems.Thm_ULHC_ind_insert
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (e : Edge) (B : Finset Edge) (x : Pt) (he : e ∉ B) :
    sidesIn (insert e B) x = sidesIn B x + if e ∈ cellE x then 1 else 0 := by
  unfold sidesIn
  rw [ind_insert he, ind_insert he, ind_insert he, ind_insert he]
  obtain ⟨p, q⟩ := x
  have key : (if e = bot (p, q) then 1 else 0) + (if e = top (p, q) then 1 else 0) +
      (if e = lft (p, q) then 1 else 0) + (if e = rgt (p, q) then 1 else 0) =
      (if e ∈ cellE (p, q) then 1 else 0 : ℕ) := by
    unfold cellE
    by_cases h1 : e = bot (p, q)
    · subst h1; simp [bot, top, lft, rgt]
    by_cases h2 : e = top (p, q)
    · subst h2; simp [bot, top, lft, rgt]
    by_cases h3 : e = lft (p, q)
    · subst h3; simp [bot, top, lft, rgt]
    by_cases h4 : e = rgt (p, q)
    · subst h4; simp [bot, top, lft, rgt]
    simp [h1, h2, h3, h4]
  omega
end ULHC
