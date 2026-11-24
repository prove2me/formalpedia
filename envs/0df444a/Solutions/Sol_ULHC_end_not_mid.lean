-- Prove2me | solution 1 for ULHC.end_not_mid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:36.677857+00:00
-- url     : https://prove2.me/submissions/fa858365-9df7-42be-8b17-6bdd1a242a34

import Definitions.Def_ULHC_TheoremA
import Definitions.Def_ULHC_V2
import Theorems.Thm_ULHC_front_corner_ne
import Theorems.Thm_ULHC_back1_cellJ_succ

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) (k : ℕ) :
    ¬ IsMid c s k (back1 (cellJ c s (k + 1)) s) ∧ ¬ IsMid c s k (front1 (cellJ c s (k + 1)) s) := by
  rw [back1_cellJ_succ]
  constructor
  · rintro ⟨j, _, hj, h | h⟩
    · exact (front_corner_ne c s (i := k) (j := j) (by omega)).1 h
    · exact (front_corner_ne c s (i := k) (j := j) (by omega)).2.1 h
  · rintro ⟨j, _, hj, h | h⟩
    · exact (front_corner_ne c s (i := k + 1) (j := j) (by omega)).1 h
    · exact (front_corner_ne c s (i := k + 1) (j := j) (by omega)).2.1 h
end ULHC
