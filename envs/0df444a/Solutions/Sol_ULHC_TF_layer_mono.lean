-- Prove2me | solution 1 for ULHC.TF.layer_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:46:28.880179+00:00
-- url     : https://prove2.me/submissions/c89b3e6d-6669-48e0-8926-ad79b140cc69

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_layer_sub_succ
import Theorems.Thm_ULHC_Conn_refl
import Theorems.Thm_ULHC_Conn_trans


set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} {k j : ℕ} (h : k ≤ j) :
    layer V F k ⊆ layer V F j := by
  induction h with
  | refl => exact Subset.refl _
  | step _ ih => exact ih.trans layer_sub_succ
end ULHC.TF
