-- Prove2me | solution 1 for ULHC.unit_shared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:04:48.821234+00:00
-- url     : https://prove2.me/submissions/57f03ad0-fc20-48ae-8035-a4132750467b

import Definitions.Def_ULHC_Conn
import Definitions.Def_ULHC_Planar
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_unit_cases
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {u v : Pt} (h : Unit u v) :
    Around u (max u.1 v.1 - 1, max u.2 v.2 - 1) ∧ Around v (max u.1 v.1 - 1, max u.2 v.2 - 1) := by
  rcases unit_cases h with h' | h' | h' | h' <;> subst h' <;>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [max_def] <;> split_ifs <;> omega
end ULHC
