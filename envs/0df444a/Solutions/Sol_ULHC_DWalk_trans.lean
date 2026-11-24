-- Prove2me | solution 1 for ULHC.DWalk.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:23.067768+00:00
-- url     : https://prove2.me/submissions/30f3f102-f9d9-4cfa-b9f2-943a95b572a8

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual

set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
namespace DWalk
theorem _root_.solution {a b c : Pt} {B B' : Finset Edge} (h : DWalk V F a b B) (h' : DWalk V F b c B') :
    DWalk V F a c (symmDiff B B') := by
  induction h with
  | nil a => rw [show symmDiff (∅ : Finset Edge) B' = B' from bot_symmDiff B']; exact h'
  | cons hs _ ih =>
    rw [symmDiff_assoc]
    exact DWalk.cons hs (ih h')
end DWalk
end ULHC
