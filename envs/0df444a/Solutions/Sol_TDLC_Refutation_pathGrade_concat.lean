-- Prove2me | solution 1 for TDLC.Refutation.pathGrade_concat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:26:29.562903+00:00
-- url     : https://prove2.me/submissions/e5cf5801-9049-47d8-9b49-8140bd8463fe

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
theorem _root_.solution {A : Type u} {x y z : A} (p : Path x y) (q : Path y z)
    (val : A → G) : pathGrade g mark (p ++ₚ q) val =
      g.mul (pathGrade g mark p val) (pathGrade g mark q val) := by
  induction p with
  | nil => exact (g.one_mul _).symm
  | seq s p ih => simp only [Path.concat, pathGrade, ih, g.assoc]
end TDLC.Refutation
