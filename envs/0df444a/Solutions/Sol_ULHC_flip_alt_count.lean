-- Prove2me | solution 1 for ULHC.flip_alt_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:21:25.082692+00:00
-- url     : https://prove2.me/submissions/cf5c42b6-4f50-422b-a795-5592b9165118

import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Cr2
import Theorems.Thm_ULHC_ACell_merge
import Theorems.Thm_ULHC_ACell_split
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Deg2_class
import Theorems.Thm_ULHC_Deg2_le_two
import Theorems.Thm_ULHC_Ends_merge
import Theorems.Thm_ULHC_flip_eq
import Theorems.Thm_ULHC_isCell_corners
import Theorems.Thm_ULHC_mkLat_cellE
import Theorems.Thm_ULHC_planar_lat


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution (hG : Deg2 V G) {u : Pt} {s : Side} (hu : IsCell V u)
    (l1 : lat1 u s ∈ G) (l2 : lat2 u s ∈ G) (hb : back u s ∉ G) (hf : front u s ∉ G) :
    (Conn G (back1 u s) (back2 u s) → ncomp V (flip G u) = ncomp V G + 1) ∧
      (¬ Conn G (back1 u s) (back2 u s) → ncomp V (flip G u) + 1 = ncomp V G) := by
  obtain ⟨ub1, ub2, uf1, uf2⟩ := isCell_corners hu s
  have hE := mkLat_cellE u s
  rw [(mkLat u s).flip_eq hE l1 l2 hb hf]
  refine ⟨fun hsame => ?_, fun hn => ?_⟩
  · exact ((mkLat u s).split hG.1 ub1 uf1 ub2 uf2 l1 l2 hb
      (fun z hz => by rcases hz with hz | hz
                      · exact hG.class ub1 hz
                      · exact hG.class ub2 hz) hsame hG.le_two
      (fun H h1 h2 h3 h4 h5 => planar_lat H u s h1 h2 h3 h4 h5)).1
  · exact ((mkLat u s).merge hG.1 ub1 ub2 l1 l2
      (fun z hz => by rcases hz with hz | hz
                      · exact hG.class ub1 hz
                      · exact hG.class ub2 hz) hn).1
end ULHC
