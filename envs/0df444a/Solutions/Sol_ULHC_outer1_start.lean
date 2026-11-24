-- Prove2me | solution 1 for ULHC.outer1_start
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:31:15.682886+00:00
-- url     : https://prove2.me/submissions/cc6ff7a3-50bb-4dad-942b-0462f1caa0b8

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
import Theorems.Thm_ULHC_corners4
import Theorems.Thm_ULHC_ind_of_mem
import Theorems.Thm_ULHC_ind_of_not_mem
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_deg_front1
import Theorems.Thm_ULHC_nb_cellJ


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F) {c : Pt} {s : Side} {n : ℕ}
include hF
namespace ULHC
theorem _root_.solution (hp : StripPat F c s n) (hn : 2 ≤ n) (hc : IsCell V c) :
    outer1 c s ∈ F := by
  obtain ⟨_, hl, hf⟩ := hp
  have h0 := hl 0 (by omega)
  have h1 := hl 1 (by omega)
  have hf0 := hf 0 (by omega)
  rw [cellJ_zero] at h0 hf0
  have hl0 : lat1 c s ∉ F := fun h => by have := h0.1.1 h; omega
  have hfr : front c s ∉ F := fun h => by have := hf0.1 h; omega
  have hl1 : lat1 (nb c s) s ∈ F := by
    rw [show nb c s = cellJ c s 1 by rw [← nb_cellJ, cellJ_zero]]; exact h1.1.2 rfl
  have hd := hF.2 _ (corners4 hc s).2.2.1
  rw [deg_front1, ind_of_not_mem hl0, ind_of_not_mem hfr, ind_of_mem hl1] at hd
  by_contra ho
  rw [ind_of_not_mem ho] at hd
  omega
end ULHC
