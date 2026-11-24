-- Prove2me | solution 1 for ULHC.TF.layer_sub_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:16.04704+00:00
-- url     : https://prove2.me/submissions/2c33d20a-c301-46f7-8843-cdb28a70c112

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_layer_succ

set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} {k : ℕ} :
    layer V F k ⊆ layer V F (k + 1) := by
  rw [layer_succ]; exact subset_union_left
end ULHC.TF
