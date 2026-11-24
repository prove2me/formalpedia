-- Prove2me | solution 1 for ULHC.cellJ_nb_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:22:40.537737+00:00
-- url     : https://prove2.me/submissions/a99fd4a8-da02-4e86-90cf-ef6069b6c6f3

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
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
namespace ULHC
theorem _root_.solution (z : Pt) (s tf : Side) (m : ℕ) : cellJ (nb z tf) s m = nb (cellJ z s m) tf := by
  obtain ⟨x, y⟩ := z
  cases s <;> cases tf <;> simp only [cellJ, nb] <;> ring_nf
end ULHC
