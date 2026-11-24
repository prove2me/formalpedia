-- Prove2me | solution 1 for ULHC.suf_patW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:07:09.063469+00:00
-- url     : https://prove2.me/submissions/6c687534-596e-4c56-92f5-02b64f12c9d6

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
import Theorems.Thm_ULHC_cellJ_add
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
theorem _root_.solution (hp : SigFrom F z.c z.s z.n i0) (hii : i0 ≤ i) (he : i % 2 = 0) (hi : i < z.n) :
    StripPat F (suf z i).c (suf z i).s (suf z i).n := by
  obtain ⟨_, _, gb, _⟩ := hp i hii hi
  refine ⟨gb.2 he, fun j hj => ?_, fun j hj => ?_⟩
  · simp only [suf] at hj
    rw [suf_cellJ]
    have := hp (i + j) (by omega) (by omega)
    simp only [suf]; constructor
    · rw [this.1]; omega
    · rw [this.2.1]; omega
  · simp only [suf] at hj ⊢
    rw [cellJ_add, (hp (i + j) (by omega) (by omega)).2.2.2]
    omega
end ULHC
