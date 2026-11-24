-- Prove2me | solution 1 for P2M_GlobalTheory_cubeFaceSequence___7c5bb83f318b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:38:29.715831+00:00
-- url     : https://prove2.me/submissions/8a5ccbfe-ec75-4ab1-970c-66ad5a833bbc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Theorems.Thm_GlobalTheory_Cube_d_termSec

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
  {e : κ ↪o ι} {i : ι}
variable (he : Set.range e = {i}ᶜ)
namespace GlobalTheory
theorem _root_.solution (A : Cube.{v} ι R) (p : ℕ) :
    (cubeFaceSequence_shortExact he A).δ p (p + 1) rfl ≫
        (shiftSuccHomologyIso (cubeComplex (Cube.upperFace e i A)) p).hom =
      (-1 : ℤ) ^ p • homologyMap (cubeComplexMap (Cube.faceMap e i A)) p := by
  let L := cubeComplex (Cube.lowerFace e A)
  let U := cubeComplex (Cube.upperFace e i A)
  let φ : L ⟶ U := cubeComplexMap (Cube.faceMap e i A)
  let σ : L.X p ⟶ (cubeComplex A).X p := cubeSecX e i A p
  have hσ : σ ≫ (cubeLowerProj e A).f p = 𝟙 _ :=
    ModuleCat.hom_ext (LinearMap.ext fun x => Cube.termLower_termSec he A x)
  have hd : σ ≫ (cubeComplex A).d p (p + 1) =
      L.d p (p + 1) ≫ cubeSecX e i A (p + 1) +
        ((-1 : ℤ) ^ p • φ.f p) ≫ cubeInclX e i A p := by
    rw [cubeComplex_d, cubeComplex_d]
    exact ModuleCat.hom_ext (LinearMap.ext fun x => Cube.d_termSec he A x)
  have key := (cubeFaceSequence_shortExact he A).δ_eq p (p + 1) rfl (L.iCycles p)
    (L.iCycles_d p (p + 1)) (L.iCycles p ≫ σ)
    ((Category.assoc _ _ _).trans ((congrArg (L.iCycles p ≫ ·) hσ).trans (Category.comp_id _)))
    (L.iCycles p ≫ ((-1 : ℤ) ^ p • φ.f p) ≫ (shiftSuccXIso U p).inv)
    (by
      change (L.iCycles p ≫ ((-1 : ℤ) ^ p • φ.f p) ≫ (shiftSuccXIso U p).inv) ≫
        (cubeUpperIncl he A).f (p + 1) = (L.iCycles p ≫ σ) ≫ (cubeComplex A).d p (p + 1)
      rw [cubeUpperIncl_f_succ, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
        Category.assoc, hd, Preadditive.comp_add, iCycles_d_assoc, zero_comp, zero_add])
    (p + 1 + 1) (by simp)
  have h1 : L.liftCycles (L.iCycles p) (p + 1) (by simp) (L.iCycles_d p (p + 1)) = 𝟙 _ := by
    rw [← cancel_mono (L.iCycles p), liftCycles_i, Category.id_comp]
  change L.liftCycles (L.iCycles p) (p + 1) _ _ ≫ L.homologyπ p ≫ _ =
    (shiftSucc U).liftCycles _ _ _ _ ≫ (shiftSucc U).homologyπ (p + 1) at key
  rw [h1, Category.id_comp] at key
  change _ = (-1 : ℤ) ^ p • homologyMap φ p
  rw [← cancel_epi (L.homologyπ p)]
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) key).trans ?_)
  rw [Category.assoc, homologyπ_extendHomologyIso_hom, Preadditive.comp_zsmul,
    homologyπ_naturality, ← Preadditive.zsmul_comp, ← Category.assoc]
  congr 1
  rw [← cancel_mono (U.iCycles p), Category.assoc, extendCyclesIso_hom_iCycles,
    liftCycles_i_assoc, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Preadditive.zsmul_comp, cyclesMap_i, Preadditive.comp_zsmul]
end GlobalTheory
