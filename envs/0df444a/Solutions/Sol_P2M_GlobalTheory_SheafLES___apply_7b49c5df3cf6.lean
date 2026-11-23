-- Prove2me | solution 1 for P2M_GlobalTheory_SheafLES___apply_7b49c5df3cf6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:39.251855+00:00
-- url     : https://prove2.me/submissions/cd93b09e-34cb-4d8c-b2fa-0f992ce13407

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
theorem _root_.solution (n : ℕ) (U : C) (x : Ext.{w'} ((freeYoneda J).obj U) S.X₃ n) :
    δ hS n U x = x.comp hS.extClass rfl := rfl
end GlobalTheory.SheafLES
