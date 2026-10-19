-- Prove2me | solution 1 for PermanentRollout.slicedGradient_kernel_avoidance_of_projective_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/b2bb63cc-19e7-4aae-8980-fffaa36c68bb

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution
    {m k : ℕ} (P : MvPolynomial (Fin m) ℂ)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (hnonzero : ∀ (u : Fin k → ℂ), u ≠ 0 →
      gradientVector P (W u) ≠ 0)
    (hdisjoint : Disjoint
      (projectiveSlicedGradientImage P W)
      ((LinearMap.ker A).projectivization : Set (ℙ ℂ (Fin m → ℂ)))) :
    ∀ (u : Fin k → ℂ), u ≠ 0 →
      gradientVector P (W u) ∉ LinearMap.ker A := by
  intro u hu hkernel
  have hgradient := hnonzero u hu
  have himage :
      Projectivization.mk ℂ (gradientVector P (W u)) hgradient ∈
        projectiveSlicedGradientImage P W :=
    ⟨u, hu, hgradient, rfl⟩
  have hprojective_kernel :
      Projectivization.mk ℂ (gradientVector P (W u)) hgradient ∈
        (LinearMap.ker A).projectivization :=
    (Submodule.mk_mem_projectivization_iff _ hgradient).mpr hkernel
  exact Set.disjoint_left.mp hdisjoint himage hprojective_kernel
end PermanentRollout
