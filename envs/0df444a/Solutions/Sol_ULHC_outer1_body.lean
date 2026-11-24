-- Prove2me | solution 1 for ULHC.outer1_body
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:00:54.590843+00:00
-- url     : https://prove2.me/submissions/4bfa00c7-db0f-4ff2-8fa9-fd3d8fd9da9b

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_strip_sig
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_corners4
import Theorems.Thm_ULHC_deg_front1
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
theorem _root_.solution {j : ℕ} (hj : j ≤ k) : outer1 (cellJ c s j) s ∈ F ↔ j % 2 = 0 := by
  obtain ⟨a1, _, _, af⟩ := strip_sig hpat (show j < k + 2 by omega)
  obtain ⟨b1, _, _, _⟩ := strip_sig hpat (show j + 1 < k + 2 by omega)
  have hd := hF.2 _ (corners4 (hcell j (by omega)) s).2.2.1
  rw [deg_front1, nb_cellJ] at hd
  have af' : front (cellJ c s j) s ∈ F ↔ j % 2 = 1 := by rw [af]; omega
  by_cases h : j % 2 = 1
  · rw [ind_of_mem (a1.2 h), ind_of_mem (af'.2 h),
      ind_of_not_mem (fun h' => by have := b1.1 h'; omega)] at hd
    constructor
    · intro ho; rw [ind_of_mem ho] at hd; omega
    · intro h'; omega
  · rw [ind_of_not_mem (fun h' => h (a1.1 h')), ind_of_not_mem (fun h' => h (af'.1 h')),
      ind_of_mem (b1.2 (by omega))] at hd
    constructor
    · intro _; omega
    · intro _; by_contra ho; rw [ind_of_not_mem ho] at hd; omega
end ULHC
