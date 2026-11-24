-- Prove2me | solution 1 for ULHC.TF.card_le_of_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:53:35.13391+00:00
-- url     : https://prove2.me/submissions/28767176-2273-43ec-b84c-533f88c9281f

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_sum_deg_black
import Theorems.Thm_ULHC_TF_sum_deg_white

set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (hF : Good V F) : F.card ≤ V.card := by
  have hB : ∑ z ∈ V.filter Black, deg F z ≤ ∑ z ∈ V.filter Black, 2 :=
    sum_le_sum fun z _ => hF.2 z
  have hW : ∑ z ∈ V.filter (fun z => ¬ Black z), deg F z ≤
      ∑ z ∈ V.filter (fun z => ¬ Black z), 2 :=
    sum_le_sum fun z _ => hF.2 z
  rw [sum_deg_black hF.1, sum_const, smul_eq_mul] at hB
  rw [sum_deg_white hF.1, sum_const, smul_eq_mul] at hW
  have := card_filter_add_card_filter_not (s := V) Black
  omega
end ULHC.TF
