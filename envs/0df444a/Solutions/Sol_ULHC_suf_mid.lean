-- Prove2me | solution 1 for ULHC.suf_mid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:06:48.407999+00:00
-- url     : https://prove2.me/submissions/6c869b21-bd07-416a-bbb4-a9c1e55ba3c1

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
import Theorems.Thm_ULHC_suf_cellJ
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
theorem _root_.solution {p : Pt} (he : i % 2 = 0)
    (h : IsMid (suf z i).c (suf z i).s ((suf z i).n - 2) p) : IsMid z.c z.s (z.n - 2) p := by
  obtain ⟨j, hj, hjk, hp⟩ := h
  simp only [suf] at hjk
  refine ⟨i + j, by omega, by omega, ?_⟩
  have := suf_cellJ (z := z) (i := i) j
  simp only [suf] at this hp ⊢
  rw [this] at hp; exact hp
end ULHC
