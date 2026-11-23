-- Prove2me | solution 1 for P2M_GlobalTheory_Flasque_subsingleton_H__of_injective_53c598f24470
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:39.050849+00:00
-- url     : https://prove2.me/submissions/946e6147-9838-4d99-a803-9bf9449361db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w v u
open GlobalTheory
open GlobalTheory.Flasque
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
variable {J}
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
open CategoryTheory Abelian Opposite Limits TopologicalSpace
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
variable {J}
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
namespace GlobalTheory.Flasque
namespace _root_.GlobalTheory.Flasque
theorem _root_.solution (I : Sheaf J AddCommGrpCat.{v}) [Injective I]
    (n : ℕ) (U : C) : Subsingleton (I.H' (n + 1) U) :=
  Ext.subsingleton_of_injective (_root_.GlobalTheory.Flasque.freeSheaf J U) I n
end _root_.GlobalTheory.Flasque
end GlobalTheory.Flasque
