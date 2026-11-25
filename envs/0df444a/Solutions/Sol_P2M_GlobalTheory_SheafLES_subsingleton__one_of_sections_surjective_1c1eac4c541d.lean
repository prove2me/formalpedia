-- Prove2me | solution 1 for P2M_GlobalTheory_SheafLES_subsingleton__one_of_sections_surjective_1c1eac4c541d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:31:43.631194+00:00
-- url     : https://prove2.me/submissions/b4f46387-9c0a-487b-8001-c16cc5cf163e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_GlobalTheory_SheafLES_map_f_one_injective_of_sections_surjective

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
theorem _root_.solution (U : C)
    (h : Function.Surjective (S.g.hom.app (op U)))
    (h₂ : Subsingleton (Sheaf.H'.{w'} S.X₂ 1 U)) : Subsingleton (Sheaf.H'.{w'} S.X₁ 1 U) :=
  (map_f_one_injective_of_sections_surjective hS U h).subsingleton
end GlobalTheory.SheafLES
