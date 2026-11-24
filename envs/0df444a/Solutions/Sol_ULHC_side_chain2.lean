-- Prove2me | solution 1 for ULHC.side_chain2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:25:27.170793+00:00
-- url     : https://prove2.me/submissions/191dde6d-84cf-4b4d-9e79-c6715c59159c

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
import Theorems.Thm_ULHC_side2_down
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_touch_side2


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i0 : ℕ} (hz : SigFrom F z tf m i0)
include hF hT hk hcell hpat hsep hz
namespace ULHC
theorem _root_.solution : ∀ j i, j ≤ k → i0 ≤ i → i < m → cellJ z tf i = nb (cellJ c s j) (latB s) →
    tf = s.opp ∧ ∃ ie, i ≤ ie ∧ ie < m ∧ ie % 2 = 0 ∧ cellJ z tf ie = nb c (latB s) := by
  intro j
  induction j with
  | zero =>
    intro i _ h0 hi hq
    obtain ⟨ht, hp, _⟩ := touch_side2 hF hT hk hcell hpat hsep hz h0 hi (j := 0) (by omega) hq
    exact ⟨ht, i, le_rfl, hi, by omega, by rw [hq, cellJ_zero]⟩
  | succ j ih =>
    intro i hj h0 hi hq
    obtain ⟨ht, _, hi1⟩ := touch_side2 hF hT hk hcell hpat hsep hz h0 hi (j := j + 1) hj hq
    obtain ⟨ht', ie, h1, h2⟩ := ih (i + 1) (by omega) (by omega) hi1 (by
      rw [← nb_cellJ, hq, ht, side2_down])
    exact ⟨ht', ie, by omega, h2⟩
end ULHC
