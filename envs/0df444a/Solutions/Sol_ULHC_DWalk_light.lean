-- Prove2me | solution 1 for ULHC.DWalk.light
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:43:01.119497+00:00
-- url     : https://prove2.me/submissions/685e42d4-2a03-4c23-a735-b856832f65e3

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
import Theorems.Thm_ULHC_DStep_light
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
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
namespace DWalk
theorem _root_.solution {a b : Pt} {B : Finset Edge} (h : DWalk V F a b B) : ∀ e ∈ B, e ∉ F := by
  induction h with
  | nil a => intro e he; simp at he
  | cons hs _ ih =>
    intro e he
    rcases Finset.mem_symmDiff.1 he with ⟨h, _⟩ | ⟨h, _⟩
    · exact hs.light e h
    · exact ih e h
end DWalk
end ULHC
