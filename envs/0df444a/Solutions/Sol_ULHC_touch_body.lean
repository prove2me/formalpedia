-- Prove2me | solution 1 for ULHC.touch_body
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:03:01.905359+00:00
-- url     : https://prove2.me/submissions/3da8bede-8ce9-4618-9ab5-a63c07660d77

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_frame_opp
import Theorems.Thm_ULHC_frame_latA
import Theorems.Thm_ULHC_frame_latB
import Theorems.Thm_ULHC_strip_sig
import Theorems.Thm_ULHC_par_of_iff
import Theorems.Thm_ULHC_ACell_ab
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
include hpat hz hi0 hi
namespace ULHC
theorem _root_.solution {j : ℕ} (hj : j ≤ k) (hq : cellJ z tf i = cellJ c s j) :
    tf = s ∧ i % 2 = j % 2 ∧ i + 1 < m := by
  obtain ⟨g1, g2, gb, gf⟩ := hz i hi0 hi
  obtain ⟨a1, a2, ab, af⟩ := strip_sig hpat (show j < k + 2 by omega)
  rw [hq] at g1 g2 gb gf
  -- In `a`'s frame the front of `c_j` is dark iff `j` is odd.
  --
  have af' : front (cellJ c s j) s ∈ F ↔ j % 2 = 1 := by rw [af]; omega
  rcases side_cases s tf with h | h | h | h <;> rw [h] at g1 g2 gb gf
  · have hp := par_of_iff (g1.symm.trans a1)
    refine ⟨h, hp, ?_⟩
    have e2 := gf.symm.trans af'
    by_contra hm
    rcases Nat.mod_two_eq_zero_or_one i with h0 | h0
    · exact absurd (e2.1 ⟨fun h' => by omega, fun h' => absurd h' hm⟩) (by omega)
    · exact hm (((e2.2 (by omega)).1) h0)
  · obtain ⟨f1, _, fb, _⟩ := frame_opp (cellJ c s j) s
    rw [f1] at g1; rw [fb] at gb
    have hp := par_of_iff (g1.symm.trans a1)
    have := gb.symm.trans af'
    exfalso
    rcases Nat.mod_two_eq_zero_or_one i with h0 | h0
    · have := this.1 h0; omega
    · have : ¬ (j % 2 = 1) := fun h' => by have := this.2 h'; omega
      omega
  · obtain ⟨_, _, fl⟩ := frame_latA (cellJ c s j) s
    exfalso
    have hbf : (back (cellJ c s j) s ∈ F ↔ front (cellJ c s j) s ∈ F) := by
      rcases fl with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1] at g1; rw [h2] at g2; exact g1.trans g2.symm
      · rw [h1] at g1; rw [h2] at g2; exact g2.trans g1.symm
    rw [ab, af'] at hbf; omega
  · obtain ⟨_, _, fl⟩ := frame_latB (cellJ c s j) s
    exfalso
    have hbf : (back (cellJ c s j) s ∈ F ↔ front (cellJ c s j) s ∈ F) := by
      rcases fl with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1] at g1; rw [h2] at g2; exact g1.trans g2.symm
      · rw [h1] at g1; rw [h2] at g2; exact g2.trans g1.symm
    rw [ab, af'] at hbf; omega
end ULHC
