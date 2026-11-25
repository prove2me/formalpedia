-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_mulMat_recover_cd4a48f275be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:01:23.245516+00:00
-- url     : https://prove2.me/submissions/0211b162-8696-4f04-b625-d7ebaf0d3f30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOnPlane
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_mulMat_sum_8087c294b09b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_recover_spec_7ca4ae570c37

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
open GroundTheory.Heights₂.Heights.DualPointsOnPlane
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T]
namespace GroundTheory.Heights₂.Heights.DualPointsOnPlane
theorem _root_.solution (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (α : 𝓞 K) (Z : T → ℂ) (s : T) :
    ∑ t, (mulMat b α s t : ℂ) * Z t =
      ∑ p : (K →+* ℂ) × Fin i, p.1 ((b s : Fin i → K) p.2) * (p.1 α * dualRecover b hb Z p) := by
  calc ∑ t, (mulMat b α s t : ℂ) * Z t
      = ∑ t, ∑ p : (K →+* ℂ) × Fin i,
          (mulMat b α s t : ℂ) * (p.1 ((b t : Fin i → K) p.2) * dualRecover b hb Z p) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [recover_spec b hb Z t, Finset.mul_sum]
    _ = ∑ p : (K →+* ℂ) × Fin i,
          (∑ t, (mulMat b α s t : ℂ) * p.1 ((b t : Fin i → K) p.2)) * dualRecover b hb Z p := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        ring
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => ?_
        have h := congrArg p.1 (mulMat_sum b α s p.2)
        simp only [map_sum, map_mul, map_intCast] at h
        rw [h]
        ring
end GroundTheory.Heights₂.Heights.DualPointsOnPlane
