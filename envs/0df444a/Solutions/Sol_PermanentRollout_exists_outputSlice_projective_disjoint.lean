-- Prove2me | solution 1 for PermanentRollout.exists_outputSlice_projective_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/d01882eb-34b6-4261-af99-65c30a527594

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_permanent_rollout_exists_output_matrix_of_smooth_homogeneous
import Theorems.Thm_PermanentRollout_projective_output_disjoint_iff
import Theorems.Thm_PermanentRollout_gradientVector_smul_of_isHomogeneous
import Theorems.Thm_PermanentRollout_gradientVector_comp_linearMap_contDiff

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution {m k d : ℕ}
    (P : MvPolynomial (Fin m) ℂ) (hP : P.IsHomogeneous d)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (hnonzero : ∀ (u : Fin k → ℂ), u ≠ 0 →
      gradientVector P (W u) ≠ 0) :
    ∃ A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ),
      Disjoint (projectiveSlicedGradientImage P W)
        ((LinearMap.ker A).projectivization : Set (ℙ ℂ (Fin m → ℂ))) := by
  obtain ⟨B, hB⟩ :=
    permanent_rollout_exists_output_matrix_of_smooth_homogeneous
      (e := d - 1)
      (fun u : Fin k → ℂ => gradientVector P (W u))
      (gradientVector_comp_linearMap_contDiff P W)
      hnonzero
      (fun a u => by
        rw [W.map_smul, gradientVector_smul_of_isHomogeneous P hP])
  refine ⟨B.mulVecLin,
    (projective_output_disjoint_iff P W B.mulVecLin hnonzero).mpr ?_⟩
  intro u hu hkernel
  apply hB u hu
  exact (LinearMap.mem_ker.mp hkernel)
end PermanentRollout
