-- Prove2me | solution 1 for ULHC.side2_facts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:19:33.100049+00:00
-- url     : https://prove2.me/submissions/09af026b-753b-4319-ab5b-bb0586e044a8

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_strip_sig
import Theorems.Thm_ULHC_outer2_body
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_back_outer2_light
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_outer2_side_nb_next
import Theorems.Thm_ULHC_side2_front
import Theorems.Thm_ULHC_side2_lat1
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i i0 : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
include hF hT hk hcell hpat hsep
namespace ULHC
theorem _root_.solution {j : ℕ} (hj : j ≤ k) :
    (lat1 (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 1) ∧
      (back (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 1) ∧
      (front (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 0) := by
  refine ⟨by rw [side2_lat1]; exact (strip_sig hpat (show j < k + 2 by omega)).2.1, ?_, ?_⟩
  · rcases j with _ | j
    · rw [cellJ_zero]
      have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
      simp only [Nat.zero_mod, zero_ne_one, iff_false]
      exact back_outer2_light hF hT hpat (by omega) hc0 hsep
    · rw [← nb_cellJ, show back (nb (nb (cellJ c s j) s) (latB s)) s = outer2 (cellJ c s j) s by
        rw [outer2_side_nb_next]; rfl, outer2_body hF hcell hpat (by omega)]; omega
  · rw [side2_front]; exact outer2_body hF hcell hpat hj
end ULHC
