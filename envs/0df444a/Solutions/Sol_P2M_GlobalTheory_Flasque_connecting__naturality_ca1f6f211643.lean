-- Prove2me | solution 1 for P2M_GlobalTheory_Flasque_connecting__naturality_ca1f6f211643
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:51:52.514799+00:00
-- url     : https://prove2.me/submissions/30724962-6ac4-4417-b605-6a72c8a207f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Theorems.Thm_GlobalTheory_Flasque_connecting_naturality

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
theorem _root_.solution {T : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hT : T.ShortExact)
    (φ : S ⟶ T) (U : C) (s : S.X₃.obj.obj (op U)) :
    connecting₀ hT U (φ.τ₃.hom.app (op U) s) =
      ((Sheaf.cohomologyPresheafFunctor J 1).map φ.τ₁).app (op U) (connecting₀ hS U s) := by
  obtain ⟨x, rfl⟩ := (sectionsEquiv S.X₃ U).surjective s
  rw [← sectionsEquiv_map, connecting₀_apply, connecting₀_apply, AddEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply]
  exact connecting_naturality hS hT φ 0 U x
end GlobalTheory.Flasque
