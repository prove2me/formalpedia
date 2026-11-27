-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjPtsOfPlane_proof_1218ef9453e2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:08:50.41657+00:00
-- url     : https://prove2.me/submissions/24a6f8f1-500b-4b68-86a0-5caf2a12060b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjPtsOfPlane
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOfPlane_map_eval__int_3dc61e60a001
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOfPlane_map_aeval_int_01a6887550a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOfPlane_eval__formPoly_18eb8109d79c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open ProjectivePointsOfPlane
namespace GroundTheory.Heights₂.Heights
namespace ProjPtsOfPlane
theorem _root_.solution : ProjPtsOfPlane.Statement := by
  intro K _ _ i σ v hv
  classical
  refine ⟨fun _ => ?_, fun f hf => ?_⟩
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
    obtain ⟨m⟩ := (integralBasis K).index_nonempty
    refine ⟨(m, j), ?_⟩
    simp only [projPlanePt]
    exact mul_ne_zero ((map_ne_zero σ).mpr ((integralBasis K).ne_zero m)) hj
  · have h0 : mConeMap (projSpaceCoord K i) f = 0 := hf
    have h1 := congrArg (MvPolynomial.eval fun _ : Unit => (1 : ProjField K i)) h0
    unfold mConeMap at h1
    rw [map_zero, map_aeval_int] at h1
    have hy : (MvPolynomial.eval fun _ : Unit => (1 : ProjField K i)) ∘
        (fun p => C (projSpaceCoord K i p) * X p.1) =
        (algebraMap (MvPolynomial (Fin i) K) (ProjField K i)) ∘ formPoly := by
      funext p
      simp [projSpaceCoord, formPoly]
    rw [hy, ← map_eval₂_int (c := Int.castRingHom _)] at h1
    have h2 : eval₂ (Int.castRingHom _) formPoly f = 0 :=
      (map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h1
    have h3 := congrArg (eval₂Hom σ v) h2
    rw [map_zero, map_eval₂_int] at h3
    have hz : (eval₂Hom σ v) ∘ formPoly = projPlanePt σ v := funext (eval₂_formPoly σ v)
    rw [hz] at h3
    rw [eval_map]
    exact h3
end ProjPtsOfPlane
end GroundTheory.Heights₂.Heights
