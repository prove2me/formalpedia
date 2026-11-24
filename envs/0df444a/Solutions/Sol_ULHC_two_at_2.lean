-- Prove2me | solution 2 for ULHC.two_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:38:44.901384+00:00
-- url     : https://prove2.me/submissions/1976b4de-b741-45f3-ac26-89a8c243a8ea

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_three_le_deg


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {A : Finset Edge} {p : Pt} {g1 g2 x : Edge} (hdeg : deg A p = 2) (h1 : g1 ∈ A)
    (h2 : g2 ∈ A) (i1 : g1.p = p ∨ g1.q = p) (i2 : g2.p = p ∨ g2.q = p) (n12 : g1 ≠ g2)
    (hx : x ∈ A) (ix : x.p = p ∨ x.q = p) : x = g1 ∨ x = g2 := by
  by_contra h
  push Not at h
  have := three_le_deg h1 h2 hx i1 i2 ix n12 (Ne.symm h.1) (Ne.symm h.2)
  omega
end ULHC
