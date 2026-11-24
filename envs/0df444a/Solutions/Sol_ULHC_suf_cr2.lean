-- Prove2me | solution 1 for ULHC.suf_cr2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:09:10.210769+00:00
-- url     : https://prove2.me/submissions/aa5202ad-3cc4-49db-92d3-fa6fcec7dad7

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
import Theorems.Thm_ULHC_suf_cellJ
import Theorems.Thm_ULHC_suf_end
import Theorems.Thm_ULHC_suf_mid
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
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
theorem _root_.solution {G : Finset Edge} {w : StripSpec} (h : CR2 V G z w) (he : i % 2 = 0)
    (hin : i + 2 ≤ z.n) : CR2 V G (suf z i) w := by
  obtain ⟨h2, hev, h1, hp, hc, hso, hne, hen, hm1, hm2, hcg, hcu⟩ := h
  have hend := suf_end (z := z) (i := i) (by omega)
  refine ⟨by simp only [suf]; omega, by simp only [suf]; omega, h1, by rw [hend]; exact hp, hc,
    ?_, by rw [hend]; exact hne, by rw [hend]; exact hen,
    fun hm => hm1 (suf_mid he hm), fun hm => hm2 (suf_mid he hm), hcg, by rw [hend]; exact hcu⟩
  intro j hj i' hi' e he1
  rw [suf_cellJ]
  simp only [suf] at hi'
  exact hso j hj (i + i') (by omega) e he1
end ULHC
