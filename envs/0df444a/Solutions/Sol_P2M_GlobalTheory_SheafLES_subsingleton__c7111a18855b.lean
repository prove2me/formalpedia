-- Prove2me | solution 1 for P2M_GlobalTheory_SheafLES_subsingleton__c7111a18855b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:46.412202+00:00
-- url     : https://prove2.me/submissions/1947fb14-217b-4fad-9f38-032d800467cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_P2M_GlobalTheory_SheafLES___injective_of_subsingleton_bddba28211f5

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
theorem _root_.solution (n : ℕ) (U : C) (h₂ : Subsingleton (Sheaf.H'.{w'} S.X₂ n U))
    (h₁ : Subsingleton (Sheaf.H'.{w'} S.X₁ (n + 1) U)) : Subsingleton (Sheaf.H'.{w'} S.X₃ n U) :=
  (δ_injective_of_subsingleton hS n U h₂).subsingleton
end GlobalTheory.SheafLES
