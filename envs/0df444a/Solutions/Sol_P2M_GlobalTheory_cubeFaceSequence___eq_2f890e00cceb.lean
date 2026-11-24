-- Prove2me | solution 1 for P2M_GlobalTheory_cubeFaceSequence___eq_2f890e00cceb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:59:03.673311+00:00
-- url     : https://prove2.me/submissions/d6db5021-4505-4854-bd6b-30f1053c046d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Theorems.Thm_P2M_GlobalTheory_cubeFaceSequence___7c5bb83f318b

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
    (cubeFaceSequence_shortExact he A).δ p (p + 1) rfl =
      homologyMap (cubeComplexMap (Cube.faceMap e i A)) p ≫
        (Int.negOnePow p • shiftSuccHomologyIso (cubeComplex (Cube.upperFace e i A)) p).inv := by
  rw [Iso.eq_comp_inv, Preadditive.smul_iso_hom, Units.smul_def, Preadditive.comp_zsmul,
    cubeFaceSequence_δ, smul_smul, Int.coe_negOnePow_natCast, ← mul_pow]
  simp
end GlobalTheory
