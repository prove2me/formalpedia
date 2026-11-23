-- Prove2me | solution 1 for P2M_GlobalTheory_SheafLES_subsingleton__430f6995ae54
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:55.425812+00:00
-- url     : https://prove2.me/submissions/cb76c31b-a5f3-41fc-a8c8-0339a18fee6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_P2M_GlobalTheory_SheafLES___surjective_of_subsingleton_5836d34aca61

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
theorem _root_.solution (n : ℕ) (U : C) (h₃ : Subsingleton (Sheaf.H'.{w'} S.X₃ n U))
    (h₂ : Subsingleton (Sheaf.H'.{w'} S.X₂ (n + 1) U)) :
    Subsingleton (Sheaf.H'.{w'} S.X₁ (n + 1) U) :=
  (δ_surjective_of_subsingleton hS n U h₂).subsingleton
end GlobalTheory.SheafLES
