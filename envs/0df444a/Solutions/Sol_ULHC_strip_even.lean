-- Prove2me | solution 1 for ULHC.strip_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:28:09.064559+00:00
-- url     : https://prove2.me/submissions/c57c2c9f-0625-47c2-9da8-10239eff30e0

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
import Theorems.Thm_ULHC_mkLat_cellE
import Theorems.Thm_ULHC_back_cellJ_succ
import Theorems.Thm_ULHC_pat_flip_last
import Theorems.Thm_ULHC_isCell_corners
import Theorems.Thm_ULHC_Deg2_le_two
import Theorems.Thm_ULHC_Deg2_class
import Theorems.Thm_ULHC_flipCol_succ
import Theorems.Thm_ULHC_strip_odd
import Theorems.Thm_ULHC_ACell_split
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_flip_eq
import Theorems.Thm_ULHC_planar_lat


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {c : Pt} {s : Side}
namespace ULHC
theorem _root_.solution (k : ℕ) (hk : k % 2 = 0) (F : Finset Edge) (hF : Deg2 V F)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
    (hsep : ¬ Conn F (back1 c s) (front1 c s))
    (hsame : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)) :
    ncomp V (flipCol F c s (k + 2)) = ncomp V F := by
  rw [flipCol_succ]
  set u := cellJ c s (k + 1)
  obtain ⟨hb, hl, hf⟩ := hpat
  have uL1 : lat1 u s ∈ F := (hl (k + 1) (by omega)).1.2 (by omega)
  have uL2 : lat2 u s ∈ F := (hl (k + 1) (by omega)).2.2 (by omega)
  have uB : back u s ∉ F := by
    rw [back_cellJ_succ]; intro h; have := (hf k (by omega)).1 h; omega
  have uF : front u s ∉ F := by
    intro h; have := (hf (k + 1) (by omega)).1 h; omega
  have hcu : IsCell V u := hcell (k + 1) le_rfl
  obtain ⟨ub1, ub2, uf1, uf2⟩ := isCell_corners hcu s
  have hE := mkLat_cellE u s
  rw [(mkLat u s).flip_eq hE uL1 uL2 uB uF]
  obtain ⟨hcount, hrel, _⟩ := (mkLat u s).split hF.1 ub1 uf1 ub2 uf2 uL1 uL2 uB
    (fun z hz => by rcases hz with hz | hz
                    · exact hF.class ub1 hz
                    · exact hF.class ub2 hz) hsame hF.le_two
    (fun G h1 h2 h3 h4 h5 => planar_lat G u s h1 h2 h3 h4 h5)
  have hF' : Deg2 V ((mkLat u s).res F) := by
    rw [← (mkLat u s).flip_eq hE uL1 uL2 uB uF]
    exact hF.flip (mkLat u s) hcu hE uL1 uL2 uB uF
  have hpat' : StripPat ((mkLat u s).res F) c s (k + 1) := by
    rw [← (mkLat u s).flip_eq hE uL1 uL2 uB uF]; exact pat_flip_last hk ⟨hb, hl, hf⟩
  have hsep' : ¬ Conn ((mkLat u s).res F) (back1 c s) (front1 c s) :=
    fun h => hsep (hrel _ _ h)
  have := (strip_odd k hk _ hF' (fun j hj => hcell j (by omega)) hpat' hsep').1
  omega
end ULHC
