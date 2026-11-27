-- Prove2me | solution 1 for P2M_GlobalTheory_Flasque_exact_connecting__map_2f4556a98bdf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:52:03.138255+00:00
-- url     : https://prove2.me/submissions/6f4ba292-e76d-48dd-8d74-bb74bb4931e5

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
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)
namespace GlobalTheory.Flasque
theorem _root_.solution (U : C) :
    Function.Exact (connecting₀ hS U)
      (((Sheaf.cohomologyPresheafFunctor J 1).map S.f).app (op U)) := by
  intro x
  refine (exact_connecting_map hS 0 U x).trans ⟨?_, ?_⟩
  · rintro ⟨y, rfl⟩
    exact ⟨sectionsEquiv S.X₃ U y, by rw [connecting₀_apply, AddEquiv.symm_apply_apply]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
end GlobalTheory.Flasque
