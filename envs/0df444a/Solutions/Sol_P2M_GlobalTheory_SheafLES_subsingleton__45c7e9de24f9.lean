-- Prove2me | solution 1 for P2M_GlobalTheory_SheafLES_subsingleton__45c7e9de24f9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:46.735933+00:00
-- url     : https://prove2.me/submissions/c8a2b448-3584-4c85-bf1b-7f35e12e8988

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__a6249fcd4aae

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
theorem _root_.solution (n : ℕ) (U : C) (h₁ : Subsingleton (Sheaf.H'.{w'} S.X₁ n U))
    (h₃ : Subsingleton (Sheaf.H'.{w'} S.X₃ n U)) : Subsingleton (Sheaf.H'.{w'} S.X₂ n U) :=
  subsingleton_of_forall_eq 0 fun x => by
    obtain ⟨y, rfl⟩ := ((exact₂ hS n U) x).1 (Subsingleton.elim _ _)
    rw [Subsingleton.elim y 0, map_zero]
end GlobalTheory.SheafLES
