-- Prove2me | solution 1 for P2M_GlobalTheory_SheafLES___res_2b8f5cf68032
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:43.25403+00:00
-- url     : https://prove2.me/submissions/0c32af6c-19d3-4645-ae3d-eb30493940e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe w' v u
open CategoryTheory Limits Abelian Opposite
noncomputable section
open GlobalTheory
open GlobalTheory.SheafLES
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)
namespace GlobalTheory.SheafLES
theorem _root_.solution (n : ℕ) {U V : C} (i : V ⟶ U) (x : Sheaf.H'.{w'} S.X₃ n U) :
    res S.X₁ (n + 1) i (δ hS n U x) = δ hS n V (res S.X₃ n i x) := by
  have (y : Ext.{w'} ((freeYoneda J).obj U) S.X₃ n) :
      (Ext.mk₀ ((freeYoneda J).map i)).comp (y.comp hS.extClass rfl) (zero_add (n + 1)) =
        ((Ext.mk₀ ((freeYoneda J).map i)).comp y (zero_add n)).comp hS.extClass rfl :=
    (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm
  exact this x
end GlobalTheory.SheafLES
