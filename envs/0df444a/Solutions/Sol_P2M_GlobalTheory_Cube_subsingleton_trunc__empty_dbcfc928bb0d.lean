-- Prove2me | solution 1 for P2M_GlobalTheory_Cube_subsingleton_trunc__empty_dbcfc928bb0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:04:26.971861+00:00
-- url     : https://prove2.me/submissions/21860639-6b7d-4b1c-a308-6ce1e38d9965

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
open GlobalTheory
open GlobalTheory.Cube
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
namespace GlobalTheory.Cube
theorem _root_.solution (A : Cube.{v} ι R) : Subsingleton ((trunc₁ A).obj ∅) :=
  subsingleton_supp A ordConnected_nonempty (by simp)
end GlobalTheory.Cube
