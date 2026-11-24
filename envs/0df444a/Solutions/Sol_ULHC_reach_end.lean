-- Prove2me | solution 1 for ULHC.reach_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:04:52.059833+00:00
-- url     : https://prove2.me/submissions/4ce0a996-6d10-4b10-ad86-c271dbc0053b

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_touch_body


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i0 : ℕ} (hz : SigFrom F z tf m i0)
include hk hpat hz
namespace ULHC
theorem _root_.solution : ∀ d i j, j + d = k + 1 → i0 ≤ i → i < m → cellJ z tf i = cellJ c s j →
    ∃ i', i ≤ i' ∧ i' < m ∧ cellJ z tf i' = cellJ c s (k + 1) := by
  intro d
  induction d with
  | zero => intro i j hd h0 hi hq; exact ⟨i, le_rfl, hi, by rw [hq, show j = k + 1 by omega]⟩
  | succ d ih =>
    intro i j hd h0 hi hq
    obtain ⟨ht, _, hi1⟩ := touch_body hpat hz h0 hi (j := j) (by omega) hq
    obtain ⟨i', h1, h2, h3⟩ := ih (i + 1) (j + 1) (by omega) (by omega) hi1 (by
      rw [← nb_cellJ, hq, ht, nb_cellJ])
    exact ⟨i', by omega, h2, h3⟩
end ULHC
