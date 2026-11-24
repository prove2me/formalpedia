-- Prove2me | solution 1 for ULHC.nOn_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:45.371086+00:00
-- url     : https://prove2.me/submissions/ba161cf5-bb57-4b25-b4f2-5f2435e12f82

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
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) (n : ℕ) (e : Edge) (J : Finset ℕ)
    (hJ : ∀ j, j < n → (e ∈ cellE (cellJ c s j) ↔ j ∈ J)) (hJn : ∀ j ∈ J, j < n) :
    nOn c s n e = J.card := by
  unfold nOn
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact (hJ j h1).1 h2
  · intro h; exact ⟨hJn j h, (hJ j (hJn j h)).2 h⟩
end ULHC
