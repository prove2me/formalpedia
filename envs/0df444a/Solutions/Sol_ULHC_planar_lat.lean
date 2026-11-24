-- Prove2me | solution 1 for ULHC.planar_lat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:32:48.996836+00:00
-- url     : https://prove2.me/submissions/dfe0a3d3-4206-48b2-ae36-bd8acc246845

import Definitions.Def_ULHC_Iso
import Definitions.Def_ULHC_Strip
import Theorems.Thm_ULHC_planar_t
import Theorems.Thm_ULHC_planar_r
import Theorems.Thm_ULHC_planar_b
import Theorems.Thm_ULHC_planar_l

set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (G : Finset Edge) (c : Pt) (s : Side) (h1 : lat1 c s ∉ G) (h2 : back c s ∉ G)
    (h3 : Conn G (front1 c s) (back2 c s)) (h4 : Conn G (front2 c s) (back1 c s))
    (h5 : ¬ Conn G (back1 c s) (front1 c s)) : False := by
  cases s
  · exact planar_b G c h1 h2 h3 h4 h5
  · exact planar_t G c h1 h2 h3 h4 h5
  · exact planar_l G c h1 h2 h3 h4 h5
  · exact planar_r G c h1 h2 h3 h4 h5
end ULHC
