-- Prove2me | solution 1 for ULHC.suf_validW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:09:10.858162+00:00
-- url     : https://prove2.me/submissions/8104da20-e0b7-4e1c-ba2f-4b3672c3c408

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
import Theorems.Thm_ULHC_suf_cells
import Theorems.Thm_ULHC_suf_patW
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {z : StripSpec} {i i0 : ℕ}
namespace ULHC
theorem _root_.solution (hp : SigFrom F z.c z.s z.n i0) (hc : ∀ j < z.n, IsCell V (cellJ z.c z.s j))
    (hii : i0 ≤ i) (he : i % 2 = 0) (hi : i < z.n)
    (hsep : ¬ Conn F (back1 (cellJ z.c z.s i) z.s) (front1 (cellJ z.c z.s i) z.s)) :
    ValidStrip V F (suf z i) :=
  ⟨by simp only [suf]; omega, suf_patW hp hii he hi, suf_cells hc, hsep⟩
end ULHC
