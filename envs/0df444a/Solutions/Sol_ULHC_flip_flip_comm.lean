-- Prove2me | solution 1 for ULHC.flip_flip_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:50:10.422007+00:00
-- url     : https://prove2.me/submissions/dd7e36ab-4af6-45ec-b2f2-402063c2dc1d

import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Cr2
import Theorems.Thm_ULHC_APair_flip


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution (G : Finset Edge) (u v : Pt) : flip (flip G u) v = flip (flip G v) u := by
  unfold flip
  rw [symmDiff_assoc, symmDiff_comm (cellE u), ← symmDiff_assoc]
end ULHC
