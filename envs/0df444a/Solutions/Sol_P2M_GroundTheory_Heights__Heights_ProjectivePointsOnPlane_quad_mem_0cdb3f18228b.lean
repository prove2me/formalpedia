-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_quad_mem_0cdb3f18228b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:52.44683+00:00
-- url     : https://prove2.me/submissions/804465b7-43a3-4557-9408-a12370b5cdac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjPtsOnPlane
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_mulMat_sum_04dda0bf4bd3

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
open GroundTheory.Heights₂.Heights.ProjectivePointsOnPlane
variable {K : Type} [Field K] [NumberField K] {i : ℕ}
namespace GroundTheory.Heights₂.Heights.ProjectivePointsOnPlane
theorem _root_.solution (α : 𝓞 K) (p q : ProjIdx K i) : quad α p q ∈ projSpaceIdeal K i := by
  have hlin : ∀ u : ProjIdx K i, ∑ n, (mulMat α u.1 n : MvPolynomial (Fin i) K) *
      (C (integralBasis K n) * X u.2) = C (α : K) * (C (integralBasis K u.1) * X u.2) := by
    intro u
    have h := congrArg (C : K → MvPolynomial (Fin i) K) (mulMat_sum α u.1)
    simp only [map_sum, map_mul, map_intCast] at h
    rw [← mul_assoc, ← h, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hS : ∀ u : ProjIdx K i, ∑ n, (mulMat α u.1 n : ProjField K i) * projSpaceCoord K i ⟨(), (n, u.2)⟩ =
      algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (C (α : K)) * projSpaceCoord K i ⟨(), u⟩ := by
    intro u
    have h := congrArg (algebraMap (MvPolynomial (Fin i) K) (ProjField K i)) (hlin u)
    simpa only [projSpaceCoord, map_sum, map_mul, map_intCast] using h
  have hsum : ∀ u : ProjIdx K i, mConeMap (projSpaceCoord K i) (lform α u) =
      MvPolynomial.C (algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (C (α : K)) *
        projSpaceCoord K i ⟨(), u⟩) * MvPolynomial.X () := by
    intro u
    rw [← hS u, lform, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [mConeMap, aeval_X, map_mul, map_intCast, eq_intCast]
    ring
  show quad α p q ∈ RingHom.ker (mConeMap (projSpaceCoord K i))
  rw [RingHom.mem_ker]
  simp only [quad, map_sub, map_mul, hsum]
  simp only [mConeMap, aeval_X]
  ring
end GroundTheory.Heights₂.Heights.ProjectivePointsOnPlane
