-- Prove2me | solution 1 for P2M_GridHam_b1_no_path__4d6679970d5b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:45:43.196672+00:00
-- url     : https://prove2.me/submissions/18224bed-8c6f-4ebd-bede-865eee9d7342

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Theorems.Thm_GridHam_hasHamPath_flipY
public import Theorems.Thm_GridHam_b1_no_path

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w : ℕ) (v : Coord) (hv : 3 ≤ v.1) : ¬ HasHamPath w 3 (1, 2) v := by
  intro h
  exact b1_no_path w (v.1, 3 - 1 - v.2) hv (hasHamPath_flipY h)
end GridHam
