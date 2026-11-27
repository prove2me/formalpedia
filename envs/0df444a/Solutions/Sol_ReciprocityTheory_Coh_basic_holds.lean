-- Prove2me | solution 1 for ReciprocityTheory.Coh.basic_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:28:00.72222+00:00
-- url     : https://prove2.me/submissions/cbe1f7d3-c0bc-4f78-b381-69a7272abb16

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Theorems.Thm_ReciprocityTheory_Coh_Cx_exists_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_H
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_comp_H
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_eq_zero_iff
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.H_cls
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_H

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
universe u
open Cx
namespace ReciprocityTheory.Coh
theorem _root_.solution : BasicStatement.{u} := by
  intro R _ A B C φ ψ n
  exact ⟨Hom.id_H n, Hom.comp_H ψ φ n, exists_cls, fun x hx => cls_eq_zero_iff hx,
    fun x hx => ⟨_, Hom.H_cls φ x hx⟩⟩
end ReciprocityTheory.Coh
