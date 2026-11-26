-- Prove2me | solution 1 for TDLC.Refutation.diagonalMarker_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:26:31.972298+00:00
-- url     : https://prove2.me/submissions/107a9758-c738-4239-9a72-66964580ca7f

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
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
theorem _root_.solution (A : Type) (a b : A) : diagonalMarker A A a b = a := by
  simp [diagonalMarker]
end TDLC.Refutation
