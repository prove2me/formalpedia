-- Prove2me | solution 1 for ULHC.touch_side1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:17:00.555375+00:00
-- url     : https://prove2.me/submissions/31a7e6cb-65e0-466e-88e8-9d6ae1207aec

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_frame_opp
import Theorems.Thm_ULHC_frame_latA
import Theorems.Thm_ULHC_frame_latB
import Theorems.Thm_ULHC_perp_bf
import Theorems.Thm_ULHC_cont_of
import Theorems.Thm_ULHC_par_of_iff
import Theorems.Thm_ULHC_side1_facts
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_side_cases


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i i0 : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
include hF hT hk hcell hpat hsep hz hi0 hi
namespace ULHC
theorem _root_.solution {j : ℕ} (hj : j ≤ k) (hq : cellJ z tf i = nb (cellJ c s j) (latA s)) :
    tf = s.opp ∧ i % 2 = j % 2 ∧ i + 1 < m := by
  obtain ⟨fn, fb, ff⟩ := side1_facts hF hT hk hcell hpat hsep hj
  obtain ⟨g1, g2, gb, gf⟩ := hz i hi0 hi
  rw [hq] at g1 g2 gb gf
  set L := nb (cellJ c s j) (latA s)
  rcases side_cases s tf with h | h | h | h <;> rw [h] at g1 g2 gb gf
  · exfalso
    have hp := par_of_iff (g2.symm.trans fn)
    rcases Nat.mod_two_eq_zero_or_one i with h0 | h0
    · have := fb.1 (gb.2 h0); omega
    · have : back L s ∈ F := fb.2 (by omega)
      have := gb.1 this; omega
  · obtain ⟨_, f2, fbk, ff'⟩ := frame_opp L s
    rw [f2] at g2; rw [ff'] at gf
    have hp := par_of_iff (g2.symm.trans fn)
    exact ⟨h, hp, cont_of gf (fb.trans (by omega))⟩
  · exfalso
    have := perp_bf g1 g2 (frame_latA L s).2.2
    rw [fb, ff] at this; omega
  · exfalso
    have := perp_bf g1 g2 (frame_latB L s).2.2
    rw [fb, ff] at this; omega
end ULHC
