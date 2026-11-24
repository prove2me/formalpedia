-- Prove2me | solution 1 for ULHC.not_mid_start
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:21:53.237524+00:00
-- url     : https://prove2.me/submissions/4838faf9-1f90-451a-af39-46d768a38ab2

import Definitions.Def_ULHC_TheoremA
import Definitions.Def_ULHC_V2
import Theorems.Thm_ULHC_corner_ne


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) (k : ℕ) :
    ¬ IsMid c s k (back1 c s) ∧ ¬ IsMid c s k (front1 c s) := by
  constructor
  · rintro ⟨j, hj, _, h | h⟩
    · exact (corner_ne c s (m := j) (by omega)).1 h
    · exact (corner_ne c s (m := j) (by omega)).2.1 h
  · rintro ⟨j, hj, _, h | h⟩
    · exact (corner_ne c s (m := j) (by omega)).2.2.1 h
    · exact (corner_ne c s (m := j) (by omega)).2.2.2 h
end ULHC
