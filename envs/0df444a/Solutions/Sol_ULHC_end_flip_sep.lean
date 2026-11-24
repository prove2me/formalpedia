-- Prove2me | solution 1 for ULHC.end_flip_sep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:40:59.523074+00:00
-- url     : https://prove2.me/submissions/d61725d0-3e09-4700-9f37-aa40132294b4

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_end_same
import Theorems.Thm_ULHC_strip_even_rel


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hF hT hk hcell hpat hsep
namespace ULHC
theorem _root_.solution : ¬ Conn (flip F (cellJ c s (k + 1))) (back1 (cellJ c s (k + 1)) s)
    (front1 (cellJ c s (k + 1)) s) := by
  obtain ⟨F1, hF1, _, hab, _⟩ := strip_even_rel k hk F hF hcell hpat hsep (end_same hT hk hcell hpat)
  rw [← hF1]; exact hab
end ULHC
