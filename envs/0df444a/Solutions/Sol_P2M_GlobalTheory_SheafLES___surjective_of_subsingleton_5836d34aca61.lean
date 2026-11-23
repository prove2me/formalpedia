-- Prove2me | solution 1 for P2M_GlobalTheory_SheafLES___surjective_of_subsingleton_5836d34aca61
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:37.213516+00:00
-- url     : https://prove2.me/submissions/efac40a9-3e5b-4f24-a4a2-52cea87b6cb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__5aa7b67be2da

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
theorem _root_.solution (n : ℕ) (U : C)
    (h : Subsingleton (Sheaf.H'.{w'} S.X₂ (n + 1) U)) : Function.Surjective (δ.{w'} hS n U) :=
  fun x => ((exact₁ hS n U) x).1 (Subsingleton.elim _ _)
end GlobalTheory.SheafLES
