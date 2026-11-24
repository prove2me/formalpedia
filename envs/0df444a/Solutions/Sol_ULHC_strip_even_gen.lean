-- Prove2me | solution 1 for ULHC.strip_even_gen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:57:14.97481+00:00
-- url     : https://prove2.me/submissions/fd5239fa-d4c7-4031-8769-977f1a68d742

import Definitions.Def_ULHC_Reroute
import Definitions.Def_ULHC_Counts
import Theorems.Thm_ULHC_strip_odd_conn
import Theorems.Thm_ULHC_ACell_merge
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Deg2_class
import Theorems.Thm_ULHC_Ends_merge
import Theorems.Thm_ULHC_back_cellJ_succ
import Theorems.Thm_ULHC_flipCol_succ
import Theorems.Thm_ULHC_flip_eq
import Theorems.Thm_ULHC_isCell_corners
import Theorems.Thm_ULHC_mkLat_cellE
import Theorems.Thm_ULHC_pat_flip_last
import Theorems.Thm_ULHC_strip_even
import Theorems.Thm_ULHC_strip_odd


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {c : Pt} {s : Side}
namespace ULHC
theorem _root_.solution (k : ℕ) (hk : k % 2 = 0) (F : Finset Edge) (hF : Deg2 V F)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
    (hsep : ¬ Conn F (back1 c s) (front1 c s)) :
    ncomp V (flipCol F c s (k + 2)) = ncomp V F ∨
      ncomp V (flipCol F c s (k + 2)) + 2 = ncomp V F := by
  by_cases hsame : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)
  · exact Or.inl (strip_even k hk F hF hcell hpat hsep hsame)
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
  obtain ⟨hcount, hrel⟩ := (mkLat u s).merge hF.1 ub1 ub2 uL1 uL2
    (fun z hz => by rcases hz with hz | hz
                    · exact hF.class ub1 hz
                    · exact hF.class ub2 hz) hsame
  have hF' : Deg2 V ((mkLat u s).res F) := by
    rw [← (mkLat u s).flip_eq hE uL1 uL2 uB uF]
    exact hF.flip (mkLat u s) hcu hE uL1 uL2 uB uF
  have hpat' : StripPat ((mkLat u s).res F) c s (k + 1) := by
    rw [← (mkLat u s).flip_eq hE uL1 uL2 uB uF]; exact pat_flip_last hk ⟨hb, hl, hf⟩
  by_cases hsep' : Conn ((mkLat u s).res F) (back1 c s) (front1 c s)
  · have := strip_odd_conn k hk _ hF' (fun j hj => hcell j (by omega)) hpat' hsep'
    left; omega
  · have := (strip_odd k hk _ hF' (fun j hj => hcell j (by omega)) hpat' hsep').1
    right; omega
end ULHC
