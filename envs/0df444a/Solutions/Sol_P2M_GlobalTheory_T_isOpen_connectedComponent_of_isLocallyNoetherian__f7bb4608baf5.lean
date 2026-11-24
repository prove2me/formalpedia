-- Prove2me | solution 1 for P2M_GlobalTheory_T_isOpen_connectedComponent_of_isLocallyNoetherian__f7bb4608baf5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:14:41.087796+00:00
-- url     : https://prove2.me/submissions/840491a5-28e2-4da9-90d2-59e410a01ae2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenConnectedComponentOfIsLocallyNoetherian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenConnectedComponentOfIsLocallyNoetherianStatement
import Theorems.Thm_GlobalTheory_isOpen_connectedComponent_of_isLocallyNoetherian


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Scheme.{0}), IsLocallyNoetherian X → ∀ x : X, IsOpen (connectedComponent x) := by
  first | exact @GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian | exact GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian | (intros; apply GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian <;> assumption)
end _root_.GlobalTheory.T
