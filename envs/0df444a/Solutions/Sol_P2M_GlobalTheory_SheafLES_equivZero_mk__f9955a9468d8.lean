-- Prove2me | solution 1 for P2M_GlobalTheory_SheafLES_equivZero_mk__f9955a9468d8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:08.168006+00:00
-- url     : https://prove2.me/submissions/e302728a-33f6-43e8-ac87-12b015c906da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_GlobalTheory_SheafLES_map_id
import Theorems.Thm_GlobalTheory_SheafLES_map_zero_hom
import Theorems.Thm_GlobalTheory_SheafLES_res_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SheafLES.map_id
attribute [local simp] GlobalTheory.SheafLES.map_zero_hom
attribute [local simp] GlobalTheory.SheafLES.res_id

set_option autoImplicit false
universe w' v u
open CategoryTheory Limits Abelian Opposite
noncomputable section
open GlobalTheory
open GlobalTheory.SheafLES
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
variable {F G K : Sheaf J AddCommGrpCat.{v}}
namespace GlobalTheory.SheafLES
theorem _root_.solution (U : C) (φ : (freeYoneda J).obj U ⟶ F) :
    equivZero.{w'} F U (Ext.mk₀ φ) = freeYonedaHomEquiv U F φ := by
  have : Ext.addEquiv₀.{w'} (Ext.mk₀ φ) = φ := by
    apply (Ext.mk₀_bijective _ _).injective
    simp
  exact congrArg (freeYonedaHomEquiv U F) this
end GlobalTheory.SheafLES
