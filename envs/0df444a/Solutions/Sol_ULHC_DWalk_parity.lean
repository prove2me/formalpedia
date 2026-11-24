-- Prove2me | solution 1 for ULHC.DWalk.parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:48:55.058816+00:00
-- url     : https://prove2.me/submissions/84f9df74-edc6-4ffb-b5de-10e488768822

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
import Theorems.Thm_ULHC_sidesIn_symmDiff
import Theorems.Thm_ULHC_sidesIn_empty
import Theorems.Thm_ULHC_DStep_parity
import Theorems.Thm_ULHC_NoTypeIII_at


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
namespace DWalk
theorem _root_.solution {a b : Pt} {B : Finset Edge} (h : DWalk V F a b B) (x : Pt)
    (hx : IsCell V x) :
    sidesIn B x % 2 = ((if x = a then 1 else 0) + (if x = b then 1 else 0)) % 2 := by
  induction h with
  | nil a => rw [sidesIn_empty]; split_ifs <;> rfl
  | cons hs _ ih =>
    rw [sidesIn_symmDiff]
    have := hs.parity x hx
    split_ifs at this ih ⊢ <;> omega
end DWalk
end ULHC
