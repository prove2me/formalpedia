-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_quad_mem_0de8153ba0b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:37.339488+00:00
-- url     : https://prove2.me/submissions/5050c4e9-e61f-4cac-b82f-eb8ffdec4aca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOnPlane
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_mulMat_sum_8087c294b09b

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
theorem _root_.solution (b : Module.Basis T ℤ (dualLattice F)) (α : 𝓞 K) (s r : T) :
    quad b α s r ∈ dualIdeal b := by
  have hlin : ∀ u, ∑ t, (mulMat b α u t : MvPolynomial (Fin i) K) *
      ∑ j, C ((b t : Fin i → K) j) * X j = C (α : K) * ∑ j, C ((b u : Fin i → K) j) * X j := by
    intro u
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h := congrArg (C : K → MvPolynomial (Fin i) K) (mulMat_sum b α u j)
    simp only [map_sum, map_mul, map_intCast] at h
    rw [← mul_assoc, ← h, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  have hS : ∀ u, ∑ t, (mulMat b α u t : ProjField K i) * dualLatticeCoord b ⟨(), t⟩ =
      algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (C (α : K)) * dualLatticeCoord b ⟨(), u⟩ := by
    intro u
    have h := congrArg (algebraMap (MvPolynomial (Fin i) K) (ProjField K i)) (hlin u)
    simpa only [dualLatticeCoord, map_sum, map_mul, map_intCast] using h
  have hsum : ∀ u, mConeMap (dualLatticeCoord b) (∑ t, C (mulMat b α u t) * X ⟨(), t⟩) =
      MvPolynomial.C (algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (C (α : K)) *
        dualLatticeCoord b ⟨(), u⟩) * MvPolynomial.X () := by
    intro u
    rw [← hS u, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [mConeMap, aeval_X, map_mul, map_intCast, eq_intCast]
    ring
  show quad b α s r ∈ RingHom.ker (mConeMap (dualLatticeCoord b))
  rw [RingHom.mem_ker]
  simp only [quad, map_sub, map_mul, hsum]
  simp only [mConeMap, aeval_X]
  ring
end GroundTheory.Heights₂.Heights.DualPointsOnPlane
