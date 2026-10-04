-- Prove2me | solution 1 for UnQuantumMechanics.hamiltonian_flow_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T03:30:25.936017+00:00
-- url     : https://prove2.me/submissions/57ff11e4-df82-4487-bd2b-7fcf9dcff0e0

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace UnQuantumMechanics

theorem flow_aux (n : ℕ) (H : Matrix (PhaseIdx n) (PhaseIdx n) ℝ)
    (ψ₀ : PhaseIdx n → ℝ) (τ : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • H) *ᵥ ψ₀)
      (H *ᵥ (NormedSpace.exp (τ • H) *ᵥ ψ₀)) τ := by
  letI : NormedRing (Matrix (PhaseIdx n) (PhaseIdx n) ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (PhaseIdx n) (PhaseIdx n) ℝ) := Matrix.linftyOpNormedAlgebra
  have h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • H)) (H * NormedSpace.exp (τ • H)) τ :=
    hasDerivAt_exp_smul_const' H τ
  let L : Matrix (PhaseIdx n) (PhaseIdx n) ℝ →L[ℝ] (PhaseIdx n → ℝ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun M => M *ᵥ ψ₀
        map_add' := fun M N => Matrix.add_mulVec M N ψ₀
        map_smul' := fun c M => Matrix.smul_mulVec c M ψ₀ }
  have h2 := L.hasFDerivAt.comp_hasDerivAt τ h1
  have h4 : L (H * NormedSpace.exp (τ • H)) = H *ᵥ (NormedSpace.exp (τ • H) *ᵥ ψ₀) := by
    show (H * NormedSpace.exp (τ • H)) *ᵥ ψ₀ = H *ᵥ (NormedSpace.exp (τ • H) *ᵥ ψ₀)
    rw [Matrix.mulVec_mulVec]
  exact h2.congr_deriv h4

end UnQuantumMechanics

open Matrix UnQuantumMechanics in
theorem solution (n : ℕ) (H : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) (hH : IsHamiltonianMatrix n H)
    (ψ₀ : PhaseIdx n → ℝ) (τ : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • H) *ᵥ ψ₀)
      (H *ᵥ (NormedSpace.exp (τ • H) *ᵥ ψ₀)) τ := by
  exact UnQuantumMechanics.flow_aux n H ψ₀ τ
