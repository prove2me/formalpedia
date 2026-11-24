-- Prove2me | solution 1 for ULHC.D_jump
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:06:00.172338+00:00
-- url     : https://prove2.me/submissions/20d9abb8-0f14-4627-a686-5f24862e0c38

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
import Theorems.Thm_ULHC_wD_supp
import Theorems.Thm_ULHC_wD_balanced
import Theorems.Thm_ULHC_pot_jump


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
  (hF : IsFactor V d F) (hH : IsFactor V d H)
include hF hH
namespace ULHC
theorem _root_.solution (e : Edge) : D F H e.hi - D F H e.lo = wD F H e :=
  pot_jump (wD_supp F H) (wD_balanced hF hH) e
end ULHC
