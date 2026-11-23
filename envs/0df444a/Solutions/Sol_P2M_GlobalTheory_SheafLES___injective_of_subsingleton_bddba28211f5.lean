-- Prove2me | solution 1 for P2M_GlobalTheory_SheafLES___injective_of_subsingleton_bddba28211f5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:17.424188+00:00
-- url     : https://prove2.me/submissions/27d8a45d-d515-4ba6-82a6-2818837ab969

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__24269ba80ece

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
    (h : Subsingleton (Sheaf.H'.{w'} S.X₂ n U)) : Function.Injective (δ.{w'} hS n U) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := ((exact₃ hS n U) x).1 hx
  rw [Subsingleton.elim y 0, map_zero]
end GlobalTheory.SheafLES
