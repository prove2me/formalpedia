-- Prove2me | solution 1 for ULHC.PStep.neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:28:49.012842+00:00
-- url     : https://prove2.me/submissions/b5480a41-1ffb-4949-be15-4bfe9618a74e

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
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
open Finset Classical
variable {V : Finset Pt} (B : Finset Edge)
namespace ULHC
namespace PStep
theorem _root_.solution {x y : Pt × Bool} (h : PStep V B x y) : PStep V B (x.1, !x.2) (y.1, !y.2) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  simp only [h2]
  cases x.2 <;> cases decide (∃ e ∈ B, Ends e x.1 y.1) <;> rfl
end PStep
end ULHC
