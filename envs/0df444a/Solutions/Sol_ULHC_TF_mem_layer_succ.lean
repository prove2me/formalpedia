-- Prove2me | solution 1 for ULHC.TF.mem_layer_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:46:06.249171+00:00
-- url     : https://prove2.me/submissions/5e68a55f-f143-455a-b8dc-bb7c64ad376d

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_layer_succ

set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} {k : ℕ} {v : Pt} :
    v ∈ layer V F (k + 1) ↔ v ∈ layer V F k ∨ ∃ u ∈ layer V F k, v ∈ nbr V F u := by
  rw [layer_succ, mem_union, mem_biUnion]
end ULHC.TF
