-- Prove2me | solution 1 for TDLC.Refutation.grade_constantBeta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:27:06.292727+00:00
-- url     : https://prove2.me/submissions/e3699ab8-3819-474a-ab8b-217bd67cafeb

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
import Theorems.Thm_TDLC_Refutation_diagonalMarker_self
import Theorems.Thm_TDLC_Path_parity_ap
import Theorems.Thm_TDLC_Path_parity_concat
import Theorems.Thm_TDLC_Path_parity_inv
import Theorems.Thm_TDLC_Path_parity_lEmbed
import Theorems.Thm_TDLC_bxor_false_left
import Theorems.Thm_TDLC_bxor_false_right
import Theorems.Thm_TDLC_bxor_self
attribute [local simp] TDLC.Path.parity_ap
attribute [local simp] TDLC.Path.parity_concat
attribute [local simp] TDLC.Path.parity_inv
attribute [local simp] TDLC.Path.parity_lEmbed
attribute [local simp] TDLC.bxor_false_left
attribute [local simp] TDLC.bxor_false_right
attribute [local simp] TDLC.bxor_self



set_option autoImplicit true
open TDLC TDLC.Refutation
universe u v
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})
namespace TDLC.Refutation
theorem _root_.solution (x a : Fin 3) :
    grade dihedral diagonalMarker (Step.beta (fun _ : Fin 3 => x) a) valuation =
      dMul (dInv (valuation x)) (valuation a) := by
  classical
  have hc : Constant (fun _ : Fin 3 => x) := fun _ _ => rfl
  simp only [grade, decide_eq_true hc, if_true, diagonalMarker_self]
  rfl
end TDLC.Refutation
