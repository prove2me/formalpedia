-- Prove2me | solution 1 for ULHC.single_pat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:28:58.726811+00:00
-- url     : https://prove2.me/submissions/3f17d664-7481-442a-b50b-d4e75940e30c

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_cellJ_zero
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {F : Finset Edge} {d : Pt} {tf : Side} (hb : back d tf ∈ F) (hl1 : lat1 d tf ∉ F)
    (hl2 : lat2 d tf ∉ F) (hf : front d tf ∈ F) : StripPat F d tf 1 := by
  refine ⟨hb, fun j hj => ?_, fun j hj => ?_⟩
  · obtain rfl : j = 0 := by omega
    rw [cellJ_zero]; simp [hl1, hl2]
  · obtain rfl : j = 0 := by omega
    rw [cellJ_zero]; simp [hf]
end ULHC
