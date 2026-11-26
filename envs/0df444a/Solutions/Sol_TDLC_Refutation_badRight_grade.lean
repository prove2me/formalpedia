-- Prove2me | solution 1 for TDLC.Refutation.badRight_grade
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:27:32.298084+00:00
-- url     : https://prove2.me/submissions/b22cbbf8-eee4-47b3-9191-6808b8c32fd1

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
import Theorems.Thm_TDLC_Refutation_pathGrade_embed
import Theorems.Thm_TDLC_Refutation_pathGrade_concat
import Theorems.Thm_TDLC_Refutation_pathGrade_ap
import Theorems.Thm_TDLC_Refutation_grade_constantBeta
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
theorem _root_.solution : pathGrade dihedral diagonalMarker badRight valuation = 2 := by
  simp only [badRight, testPath, testStep, badFamily, pathGrade_concat,
    pathGrade_ap, pathGrade_embed]
  change dMul (grade dihedral diagonalMarker (Step.beta (fun _ : Fin 3 => 0) 1) valuation)
    (grade dihedral diagonalMarker (Step.beta (fun _ : Fin 3 => 0) 2) valuation) = 2
  rw [grade_constantBeta, grade_constantBeta]
  decide
end TDLC.Refutation
