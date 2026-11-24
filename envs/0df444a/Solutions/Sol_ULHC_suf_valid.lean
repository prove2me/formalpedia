-- Prove2me | solution 1 for ULHC.suf_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:08:55.132524+00:00
-- url     : https://prove2.me/submissions/31795d49-2a08-47b4-aca7-7b13c4997918

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
import Theorems.Thm_ULHC_suf_pat
import Theorems.Thm_ULHC_suf_cells
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
theorem _root_.solution (hp : StripPat F z.c z.s z.n) (hc : ∀ j < z.n, IsCell V (cellJ z.c z.s j))
    (he : i % 2 = 0) (hi : i < z.n)
    (hsep : ¬ Conn F (back1 (cellJ z.c z.s i) z.s) (front1 (cellJ z.c z.s i) z.s)) :
    ValidStrip V F (suf z i) :=
  ⟨by simp only [suf]; omega, suf_pat hp he hi, suf_cells hc, hsep⟩
end ULHC
