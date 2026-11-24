-- Prove2me | solution 1 for ULHC.w_zero_at_missing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:22:37.096799+00:00
-- url     : https://prove2.me/submissions/714c7756-f90d-4803-bedd-395726157bed

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain

set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {E : Finset Edge} {w : Edge → ℤ}
  (hS : Supp E w) (hb : Balanced w) (hE : ∀ e ∈ E, e.p ∈ V ∧ e.q ∈ V)
include hS hb hE
omit hb
namespace ULHC
theorem _root_.solution {a : Pt} (ha : a ∉ V) {e : Edge} (h : e.p = a ∨ e.q = a) : w e = 0 := by
  apply hS
  intro he
  rcases h with h | h
  · exact ha (h ▸ (hE e he).1)
  · exact ha (h ▸ (hE e he).2)
end ULHC
