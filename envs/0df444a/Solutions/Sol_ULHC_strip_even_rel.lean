-- Prove2me | solution 1 for ULHC.strip_even_rel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:28:00.658672+00:00
-- url     : https://prove2.me/submissions/e82e8bb6-4d9c-4c2a-92e9-6914864e2631

import Definitions.Def_ULHC_TheoremA
import Definitions.Def_ULHC_V2
import Theorems.Thm_ULHC_ACell_split
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Deg2_class
import Theorems.Thm_ULHC_Deg2_le_two
import Theorems.Thm_ULHC_back_cellJ_succ
import Theorems.Thm_ULHC_flipCol_succ
import Theorems.Thm_ULHC_flip_eq
import Theorems.Thm_ULHC_isCell_corners
import Theorems.Thm_ULHC_mkLat_cellE
import Theorems.Thm_ULHC_ncomp_congr
import Theorems.Thm_ULHC_pat_flip_last
import Theorems.Thm_ULHC_planar_lat
import Theorems.Thm_ULHC_strip_odd


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {c : Pt} {s : Side}
namespace ULHC
theorem _root_.solution (k : ℕ) (hk : k % 2 = 0) (F : Finset Edge) (hF : Deg2 V F)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
    (hsep : ¬ Conn F (back1 c s) (front1 c s))
    (hsame : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)) :
    ∃ F1 : Finset Edge, F1 = flip F (cellJ c s (k + 1)) ∧
      flipCol F c s (k + 2) = flipCol F1 c s (k + 1) ∧
      ¬ Conn F1 (back1 (cellJ c s (k + 1)) s) (front1 (cellJ c s (k + 1)) s) ∧
      (∀ x y, Conn F1 x y → Conn F x y) ∧
      (∀ x y, Conn F x y ↔ Conn F1 x y ∨
        (Conn F1 x (back1 (cellJ c s (k + 1)) s) ∧ Conn F1 (front1 (cellJ c s (k + 1)) s) y) ∨
        (Conn F1 x (front1 (cellJ c s (k + 1)) s) ∧ Conn F1 (back1 (cellJ c s (k + 1)) s) y)) ∧
      ∀ x y, ¬ IsMid c s k x → ¬ IsMid c s k y →
        (Conn (flipCol F c s (k + 2)) x y ↔ Conn F1 x y ∨
          (Conn F1 x (back1 c s) ∧ Conn F1 (front1 c s) y) ∨
          (Conn F1 x (front1 c s) ∧ Conn F1 (back1 c s) y)) := by
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
  have hflip := (mkLat u s).flip_eq hE uL1 uL2 uB uF
  obtain ⟨hcount, hrel, hfine⟩ := (mkLat u s).split hF.1 ub1 uf1 ub2 uf2 uL1 uL2 uB
    (fun z hz => by rcases hz with hz | hz
                    · exact hF.class ub1 hz
                    · exact hF.class ub2 hz) hsame hF.le_two
    (fun G h1 h2 h3 h4 h5 => planar_lat G u s h1 h2 h3 h4 h5)
  set F1 := (mkLat u s).res F
  have hF' : Deg2 V F1 := by
    rw [← hflip]; exact hF.flip (mkLat u s) hcu hE uL1 uL2 uB uF
  have hpat' : StripPat F1 c s (k + 1) := by
    rw [← hflip]; exact pat_flip_last hk ⟨hb, hl, hf⟩
  have hsep' : ¬ Conn F1 (back1 c s) (front1 c s) := fun h => hsep (hrel _ _ h)
  have hab : ¬ Conn F1 (back1 u s) (front1 u s) := by
    intro h
    have : ncomp V F1 = ncomp V F := by
      apply ncomp_congr
      intro x _ y _
      rw [hfine x y]
      constructor
      · exact fun h' => Or.inl h'
      · rintro (h' | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact h'
        · exact (h1.trans h).trans h2
        · exact (h1.trans h.symm).trans h2
    omega
  refine ⟨F1, hflip.symm, by rw [flipCol_succ, hflip], hab, hrel, hfine, ?_⟩
  intro x y hx hy
  rw [flipCol_succ, hflip]
  exact (strip_odd k hk F1 hF' (fun j hj => hcell j (by omega)) hpat' hsep').2 x y hx hy
end ULHC
