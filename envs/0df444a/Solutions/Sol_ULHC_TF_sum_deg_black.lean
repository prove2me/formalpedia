-- Prove2me | solution 1 for ULHC.TF.sum_deg_black
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:51:50.662772+00:00
-- url     : https://prove2.me/submissions/07c6da8c-cf6a-4593-9323-52f7a1d6c6fc

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_black_q
import Theorems.Thm_ULHC_TF_sum_deg
import Theorems.Thm_ULHC_TF_no_edge_black

set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (hF : Inside V F) :
    ∑ z ∈ V.filter Black, deg F z = F.card := by
  rw [sum_deg (no_edge_black fun z hz => (mem_filter.1 hz).2), filter_true_of_mem]
  intro e he
  by_cases h : Black e.p
  · exact Or.inl (mem_filter.2 ⟨(hF e he).1, h⟩)
  · exact Or.inr (mem_filter.2 ⟨(hF e he).2, (black_q e).2 h⟩)
end ULHC.TF
