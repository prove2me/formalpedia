-- Prove2me | solution 1 for P2M_GlobalTheory_mono_cubeFaceSequence___iff_45ee17f4c004
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:21:27.644589+00:00
-- url     : https://prove2.me/submissions/6ae8012d-4edc-4f14-ad29-73de82673289

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Theorems.Thm_P2M_GlobalTheory_cubeFaceSequence___eq_2f890e00cceb

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
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
  {e : κ ↪o ι} {i : ι} (he : Set.range e = {i}ᶜ)
include he
namespace GlobalTheory
theorem _root_.solution (A : Cube.{v} ι R) (p : ℕ) :
    Mono ((cubeFaceSequence_shortExact he A).δ p (p + 1) rfl) ↔
      Mono (homologyMap (cubeComplexMap (Cube.faceMap e i A)) p) := by
  rw [cubeFaceSequence_δ_eq]
  exact ⟨fun h => @mono_of_mono _ _ _ _ _ _ _ h, fun _ => mono_comp _ _⟩
end GlobalTheory
