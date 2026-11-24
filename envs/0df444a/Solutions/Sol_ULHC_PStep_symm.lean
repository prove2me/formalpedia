-- Prove2me | solution 1 for ULHC.PStep.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:30:13.124143+00:00
-- url     : https://prove2.me/submissions/a833023d-2103-42a0-92ea-c84efbb41cbf

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_ends_swap_iff
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
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
theorem _root_.solution {x y : Pt × Bool} (h : PStep V B x y) : PStep V B y x := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1.symm, ?_⟩
  rw [h2, show decide (∃ e ∈ B, Ends e y.1 x.1) = decide (∃ e ∈ B, Ends e x.1 y.1) from
    by simp only [ends_swap_iff B]]
  cases x.2 <;> cases decide (∃ e ∈ B, Ends e x.1 y.1) <;> rfl
end PStep
end ULHC
