-- Prove2me | solution 1 for P2M_GlobalTheory_T_geometricallyConnected_of_smooth_of_section__4d32d1b5add3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:37.906643+00:00
-- url     : https://prove2.me/submissions/70830c63-2f5c-4f9a-b741-f36289478a68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GeometricallyConnectedOfSmoothOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GeometricallyConnectedOfSmoothOfSectionStatement
import Theorems.Thm_GlobalTheory_geometricallyConnected_of_smooth_of_section


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
theorem _root_.solution : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (e : Spec (CommRingCat.of k) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → ConnectedSpace X → GeometricallyConnected f := by
  first | exact @GlobalTheory.geometricallyConnected_of_smooth_of_section | exact GlobalTheory.geometricallyConnected_of_smooth_of_section | (intros; apply GlobalTheory.geometricallyConnected_of_smooth_of_section <;> assumption)
end _root_.GlobalTheory.T
