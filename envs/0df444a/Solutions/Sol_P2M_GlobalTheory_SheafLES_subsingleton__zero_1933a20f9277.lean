-- Prove2me | solution 1 for P2M_GlobalTheory_SheafLES_subsingleton__zero_1933a20f9277
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:31:47.046009+00:00
-- url     : https://prove2.me/submissions/afb0f8de-ab1e-402b-bc3d-45cfda96f65c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_GlobalTheory_SheafLES_injective_zero

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
include hS
namespace GlobalTheory.SheafLES
theorem _root_.solution (U : C) (h₂ : Subsingleton (Sheaf.H'.{w'} S.X₂ 0 U)) :
    Subsingleton (Sheaf.H'.{w'} S.X₁ 0 U) :=
  (injective_zero hS U).subsingleton
end GlobalTheory.SheafLES
