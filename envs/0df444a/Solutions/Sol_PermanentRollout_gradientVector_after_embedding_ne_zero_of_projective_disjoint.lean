-- Prove2me | solution 1 for PermanentRollout.gradientVector_after_embedding_ne_zero_of_projective_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/8bcab780-bd77-46b0-bd36-3df4a992bd5f

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_gradientVector_eq_zero_iff
import Theorems.Thm_PermanentRollout_mk_mem_projectiveCriticalLocus

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
    (hW : Function.Injective W)
    (hdisjoint : Disjoint
      ((LinearMap.range W).projectivization : Set (ℙ ℂ (Fin m → ℂ)))
      (projectiveCriticalLocus P))
    (u : Fin k → ℂ) (hu : u ≠ 0) :
    gradientVector P (W u) ≠ 0 := by
  intro hgradient
  have hWu : W u ≠ 0 := by
    intro hzero
    exact hu (hW (by simpa using hzero))
  have hpoint_range :
      Projectivization.mk ℂ (W u) hWu ∈
        (LinearMap.range W).projectivization :=
    (Submodule.mk_mem_projectivization_iff _ hWu).mpr ⟨u, rfl⟩
  have hpoint_critical :
      Projectivization.mk ℂ (W u) hWu ∈ projectiveCriticalLocus P :=
    mk_mem_projectiveCriticalLocus P (W u) hWu
      ((gradientVector_eq_zero_iff P (W u)).mp hgradient)
  exact Set.disjoint_left.mp hdisjoint hpoint_range hpoint_critical
end PermanentRollout
