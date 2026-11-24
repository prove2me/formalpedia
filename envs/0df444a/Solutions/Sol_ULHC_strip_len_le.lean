-- Prove2me | solution 1 for ULHC.strip_len_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:50:47.653482+00:00
-- url     : https://prove2.me/submissions/28dbd579-cd90-4cde-874c-6e86cba53fa9

import Definitions.Def_ULHC_CrPath
import Definitions.Def_ULHC_Comp
import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_Enum
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_cellJ_inj
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side)
variable {V F c s}
namespace ULHC
theorem _root_.solution {n : ℕ} (h : ∀ j < n, IsCell V (cellJ c s j)) : n ≤ V.card := by
  have hmaps : ∀ k ∈ Finset.range n, cellJ c s k ∈ V := fun k hk =>
    (h k (Finset.mem_range.1 hk)).1
  have hinj : Set.InjOn (cellJ c s) (Finset.range n) := fun i _ j _ hij => cellJ_inj c s hij
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  simpa using this
end ULHC
