-- Prove2me | solution 1 for ULHC.back1_not_side2_corner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:03:38.248362+00:00
-- url     : https://prove2.me/submissions/634e8a0d-9a3c-4751-aee4-ffd371859847

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
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
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) :
    back1 c s ∉ ({back1 (nb c (latB s)) s, back2 (nb c (latB s)) s, front1 (nb c (latB s)) s,
      front2 (nb c (latB s)) s} : Finset Pt) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [back1, back2, front1, front2, latB, nb] <;> omega
end ULHC
