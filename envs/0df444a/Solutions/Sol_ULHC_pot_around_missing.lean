-- Prove2me | solution 1 for ULHC.pot_around_missing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:24:59.757688+00:00
-- url     : https://prove2.me/submissions/c4f86b05-5f92-4d3d-9785-509ce7e7b394

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_w_zero_at_missing
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_pot_around
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {E : Finset Edge} {w : Edge → ℤ}
  (hS : Supp E w) (hb : Balanced w) (hE : ∀ e ∈ E, e.p ∈ V ∧ e.q ∈ V)
include hS hb hE
namespace ULHC
theorem _root_.solution {a c : Pt} (ha : a ∉ V) (hc : Around a c) : pot E w c = pot E w a := by
  apply pot_around hS hb _ hc
  obtain ⟨x, y⟩ := a
  refine ⟨w_zero_at_missing hS hE ha (Or.inl rfl), w_zero_at_missing hS hE ha (Or.inl rfl),
    w_zero_at_missing hS hE ha (Or.inr ?_), w_zero_at_missing hS hE ha (Or.inr ?_)⟩ <;>
    simp [eL, eD, Edge.q]
end ULHC
