-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualPtsOfPlane_proof_4394ca2b9395
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:51.761841+00:00
-- url     : https://prove2.me/submissions/e5ba537c-ab64-48a4-be79-a180afb7ea6d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOfPlane
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_map_eval__int_cf6927fb8f20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_map_aeval_int_f4689206ea1e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_dualPlanePt_eq_mulVec_bac7c6c6467c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_eval__formPoly_b2721da1c34e

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
open DualPointsOfPlane
namespace GroundTheory.Heights₂.Heights
namespace DualPtsOfPlane
theorem _root_.solution : DualPtsOfPlane.Statement := by
  intro K _ _ i F T _ _ b hb σ v hv
  classical
  refine ⟨fun _ => ?_, fun f hf => ?_⟩
  · have hw : (fun p : (K →+* ℂ) × Fin i => if p.1 = σ then v p.2 else 0) ≠ 0 := by
      intro h0
      apply hv
      funext j
      simpa using congrFun h0 (σ, j)
    have hne : dualEmbMatrix b *ᵥ (fun p : (K →+* ℂ) × Fin i => if p.1 = σ then v p.2 else 0) ≠ 0 := by
      intro h0
      apply hw
      apply hb.1
      rw [map_zero, Matrix.mulVecLin_apply]
      exact h0
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hne
    exact ⟨t, by rw [dualPlanePt_eq_mulVec]; exact ht⟩
  · have h0 : mConeMap (dualLatticeCoord b) f = 0 := hf
    have h1 := congrArg (MvPolynomial.eval fun _ : Unit => (1 : ProjField K i)) h0
    unfold mConeMap at h1
    rw [map_zero, map_aeval_int] at h1
    have hy : (MvPolynomial.eval fun _ : Unit => (1 : ProjField K i)) ∘
        (fun p => C (dualLatticeCoord b p) * X p.1) =
        (algebraMap (MvPolynomial (Fin i) K) (ProjField K i)) ∘ formPoly b := by
      funext p
      simp [dualLatticeCoord, formPoly]
    rw [hy, ← map_eval₂_int (c := Int.castRingHom _)] at h1
    have h2 : eval₂ (Int.castRingHom _) (formPoly b) f = 0 :=
      (map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h1
    have h3 := congrArg (eval₂Hom σ v) h2
    rw [map_zero, map_eval₂_int] at h3
    have hz : (eval₂Hom σ v) ∘ formPoly b = dualPlanePt b σ v := funext (eval₂_formPoly b σ v)
    rw [hz] at h3
    rw [eval_map]
    exact h3
end DualPtsOfPlane
end GroundTheory.Heights₂.Heights
