-- Prove2me | solution 1 for P2M_GlobalTheory_SheafLES___equivZero_symm_eq_zero_iff_47a22b9ce459
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:44.417806+00:00
-- url     : https://prove2.me/submissions/1a935355-354d-406f-ae53-fe68514cd81c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_GlobalTheory_SheafLES_equivZero_map
import Theorems.Thm_GlobalTheory_SheafLES_map_equivZero_symm
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
theorem _root_.solution (U : C) (s : S.X₃.obj.obj (op U)) :
    δ.{w'} hS 0 U ((equivZero S.X₃ U).symm s) = 0 ↔ ∃ t, S.g.hom.app (op U) t = s := by
  rw [exact₃ hS 0 U]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨equivZero S.X₂ U x, by rw [← equivZero_map, hx, AddEquiv.apply_symm_apply]⟩
  · rintro ⟨t, rfl⟩
    exact ⟨_, map_equivZero_symm S.g U t⟩
end GlobalTheory.SheafLES
