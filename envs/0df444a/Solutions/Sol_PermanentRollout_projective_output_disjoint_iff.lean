-- Prove2me | solution 1 for PermanentRollout.projective_output_disjoint_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/7b381b4d-609a-4612-9f57-8cb3508e5711

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_slicedGradient_kernel_avoidance_of_projective_disjoint

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution {m k : ℕ}
    (P : MvPolynomial (Fin m) ℂ)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (hnonzero : ∀ (u : Fin k → ℂ), u ≠ 0 →
      gradientVector P (W u) ≠ 0) :
    Disjoint (projectiveSlicedGradientImage P W)
      ((LinearMap.ker A).projectivization : Set (ℙ ℂ (Fin m → ℂ))) ↔
      ∀ (u : Fin k → ℂ), u ≠ 0 →
        gradientVector P (W u) ∉ LinearMap.ker A := by
  constructor
  · exact slicedGradient_kernel_avoidance_of_projective_disjoint
      P W A hnonzero
  · intro havoid
    apply Set.disjoint_left.mpr
    intro point hpoint_image hpoint_kernel
    obtain ⟨u, hu, hgradient, hpoint⟩ := hpoint_image
    rw [← hpoint] at hpoint_kernel
    exact havoid u hu
      ((Submodule.mk_mem_projectivization_iff _ hgradient).mp hpoint_kernel)
end PermanentRollout
