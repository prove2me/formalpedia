-- Prove2me | solution 1 for TDLC.Refutation.pathGrade_ap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:26:30.012346+00:00
-- url     : https://prove2.me/submissions/6c08923c-7177-4895-9c22-f41551e13f73

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
theorem _root_.solution {A B : Type u} (f : A → B) {x y : A}
    (p : Path x y) (val : B → G) :
    pathGrade g mark (Path.ap f p) val = pathGrade g mark p (fun x => val (f x)) := by
  induction p with
  | nil => rfl
  | seq s p ih => simp only [Path.ap, pathGrade, grade, ih]
end TDLC.Refutation
