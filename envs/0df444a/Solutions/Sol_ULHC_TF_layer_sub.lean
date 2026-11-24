-- Prove2me | solution 1 for ULHC.TF.layer_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:49:55.725795+00:00
-- url     : https://prove2.me/submissions/c58527a5-0e80-46a7-8042-2fa0ed2afee7

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_layer_succ
import Theorems.Thm_ULHC_TF_nbr_sub

set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (k : ℕ) : layer V F k ⊆ V := by
  induction k with
  | zero => exact filter_subset _ _
  | succ k ih =>
    rw [layer_succ]
    exact union_subset ih (biUnion_subset.2 fun u _ => nbr_sub u)
end ULHC.TF
