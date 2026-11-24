-- Prove2me | solution 1 for ULHC.cncomp_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:56:05.752281+00:00
-- url     : https://prove2.me/submissions/667cbec4-00f3-4e8e-8a83-a357b879c5ca

import Definitions.Def_ULHC_TwoFactor
import Definitions.Def_ULHC_Comp
import Theorems.Thm_ULHC_ccls_eq

set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
theorem _root_.solution (hFV : Inside V F) : cncomp V F = ncomp V F := by
  classical
  unfold cncomp ncomp
  congr 1
  exact image_congr (fun x hx => ccls_eq hFV hx)
end ULHC
