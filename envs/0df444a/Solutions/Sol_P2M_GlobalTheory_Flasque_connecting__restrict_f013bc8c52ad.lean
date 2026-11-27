-- Prove2me | solution 1 for P2M_GlobalTheory_Flasque_connecting__restrict_f013bc8c52ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:51:56.87213+00:00
-- url     : https://prove2.me/submissions/4ae881e5-e0fd-48e0-be8f-b6f6eb0fc988

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Theorems.Thm_GlobalTheory_Flasque_sectionsEquiv_restrict
import Theorems.Thm_GlobalTheory_Flasque_connecting_restrict

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
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)
namespace GlobalTheory.Flasque
theorem _root_.solution {V U : C} (i : V ⟶ U) (s : S.X₃.obj.obj (op U)) :
    connecting₀ hS V (S.X₃.obj.map i.op s) =
      (S.X₁.cohomologyPresheaf 1).map i.op (connecting₀ hS U s) := by
  obtain ⟨x, rfl⟩ := (sectionsEquiv S.X₃ U).surjective s
  rw [← sectionsEquiv_restrict, connecting₀_apply, connecting₀_apply, AddEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply]
  exact connecting_restrict hS 0 i x
end GlobalTheory.Flasque
