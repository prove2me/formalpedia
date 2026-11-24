-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_inv_mem_SU_8fcf949bf882
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:44.65673+00:00
-- url     : https://prove2.me/submissions/9d8262cc-39ec-4fbc-9c0b-ee62c5661daa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_LocGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_DenseRangeFiniteAdele
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open QuadraticAlgebra GroundTheory.Heights₂.Theta GroundTheory.Automorphic
attribute [local instance] topAE
attribute [local instance] isModuleTopology_AE
namespace GroundTheory.Heights₂.Heights.StrongApprox
theorem _root_.solution {R : Type*} [CommRing R] (σ : R →+* R) {N : ℕ} (J : Matrix (Fin N) (Fin N) R)
    {a : Matrix (Fin N) (Fin N) R} (ha : a ∈ SU σ J) : a⁻¹ ∈ SU σ J := by
  obtain ⟨hdet, hu⟩ := ha
  have hunit : IsUnit a.det := by rw [hdet]; exact isUnit_one
  have hmap : a.map σ * a⁻¹.map σ = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hunit, Matrix.map_one _ (map_zero σ) (map_one σ)]
  refine ⟨by rw [Matrix.det_nonsing_inv, hdet, Ring.inverse_one], ?_⟩
  calc a⁻¹ᵀ * J * a⁻¹.map σ = a⁻¹ᵀ * (aᵀ * J * a.map σ) * a⁻¹.map σ := by rw [hu]
    _ = (a * a⁻¹)ᵀ * J * (a.map σ * a⁻¹.map σ) := by
        rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [Matrix.mul_nonsing_inv _ hunit, hmap]; simp
end GroundTheory.Heights₂.Heights.StrongApprox
