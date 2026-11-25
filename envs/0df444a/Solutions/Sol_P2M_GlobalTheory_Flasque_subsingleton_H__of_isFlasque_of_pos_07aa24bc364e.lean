-- Prove2me | solution 1 for P2M_GlobalTheory_Flasque_subsingleton_H__of_isFlasque_of_pos_07aa24bc364e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:31:58.036471+00:00
-- url     : https://prove2.me/submissions/1ab42a20-14c5-42e0-8dd7-081dbb613bc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Theorems.Thm_P2M_GlobalTheory_Flasque_subsingleton_H__of_isFlasque_199e9bf4dfbd

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
variable {X : TopCat.{u}}
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
open CategoryTheory Abelian Opposite Limits TopologicalSpace
variable {X : TopCat.{u}}
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
namespace GlobalTheory.Flasque
namespace _root_.GlobalTheory.Flasque
theorem _root_.solution (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [F.IsFlasque] {n : ℕ} (hn : 0 < n) (U : Opens X) : Subsingleton (F.H' n U) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  exact _root_.GlobalTheory.Flasque.subsingleton_H'_of_isFlasque F m U
end _root_.GlobalTheory.Flasque
end GlobalTheory.Flasque
