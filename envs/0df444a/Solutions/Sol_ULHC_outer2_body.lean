-- Prove2me | solution 1 for ULHC.outer2_body
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:00:59.8957+00:00
-- url     : https://prove2.me/submissions/0fab843e-b2d0-428b-831c-b435cc995a42

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_strip_sig
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_corners4
import Theorems.Thm_ULHC_deg_front2
import Theorems.Thm_ULHC_ind_of_mem
import Theorems.Thm_ULHC_ind_of_not_mem
import Theorems.Thm_ULHC_nb_cellJ


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i i0 : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
include hF hpat hcell
namespace ULHC
theorem _root_.solution {j : ℕ} (hj : j ≤ k) : outer2 (cellJ c s j) s ∈ F ↔ j % 2 = 0 := by
  obtain ⟨_, a2, _, af⟩ := strip_sig hpat (show j < k + 2 by omega)
  obtain ⟨_, b2, _, _⟩ := strip_sig hpat (show j + 1 < k + 2 by omega)
  have hd := hF.2 _ (corners4 (hcell j (by omega)) s).2.2.2
  rw [deg_front2, nb_cellJ] at hd
  have af' : front (cellJ c s j) s ∈ F ↔ j % 2 = 1 := by rw [af]; omega
  by_cases h : j % 2 = 1
  · rw [ind_of_mem (a2.2 h), ind_of_mem (af'.2 h),
      ind_of_not_mem (fun h' => by have := b2.1 h'; omega)] at hd
    constructor
    · intro ho; rw [ind_of_mem ho] at hd; omega
    · intro h'; omega
  · rw [ind_of_not_mem (fun h' => h (a2.1 h')), ind_of_not_mem (fun h' => h (af'.1 h')),
      ind_of_mem (b2.2 (by omega))] at hd
    constructor
    · intro _; omega
    · intro _; by_contra ho; rw [ind_of_not_mem ho] at hd; omega
end ULHC
