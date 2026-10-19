-- Prove2me | solution 1 for PermanentRollout.exists_injective_inputMap_into_linearCoordinateKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/2c260a4e-48a1-4011-bb55-b783f9b32f03

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {m k n : ℕ} (c : Fin n → Fin m → ℂ)
    (hk : k + n ≤ m) :
    ∃ W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ),
      Function.Injective W ∧
        ∀ u : Fin k → ℂ, (Matrix.mulVecLin
          (c : Matrix (Fin n) (Fin m) ℂ) :
          (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (W u) = 0 := by
  let L : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    Matrix.mulVecLin (c : Matrix (Fin n) (Fin m) ℂ)
  have hrange : Module.finrank ℂ (LinearMap.range L) ≤ n := by
    simpa using (LinearMap.range L).finrank_le
  have hnullity :
      Module.finrank ℂ (LinearMap.range L) +
        Module.finrank ℂ (LinearMap.ker L) = m := by
    simpa using L.finrank_range_add_finrank_ker
  have hkernel : k ≤ Module.finrank ℂ (LinearMap.ker L) := by
    omega
  have hsource :
      Module.finrank ℂ (Fin k → ℂ) ≤
        Module.finrank ℂ (LinearMap.ker L) := by
    simpa using hkernel
  obtain ⟨f, hf⟩ := finrank_le_iff_exists_linearMap.mp hsource
  refine ⟨(LinearMap.ker L).subtype.comp f,
    Subtype.val_injective.comp hf, ?_⟩
  intro u
  exact (f u).property
end PermanentRollout
