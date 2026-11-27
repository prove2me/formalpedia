-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_SAOpenHolds_hyps_24f5835ce3b9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:08:33.701869+00:00
-- url     : https://prove2.me/submissions/12de4c8d-1583-4c02-947f-f3f7acc9487a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_LocGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_DenseRangeFiniteAdele
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_gauss_finrank_b2407f5ee816
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_gauss_conj_ne_one_e84154cc7c34
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_hypPlane_herm_5ea1193b1153
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_hypPlane_unit_65a5a7802c0c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_gauss_isotropic_e16bc12fb6a2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_gA_mem_SU_40ec3b5d6c7a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_inv_mem_SU_8fcf949bf882
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_mul_mem_SU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_one_mem_SU


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
namespace SAOpenHolds
theorem _root_.solution :
    let Kg := SU (sigA (conj ℚ GaussQ)) (hypPlane.map (inclA ℚ GaussQ))
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧ hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ) ∧
      IsUnit hypPlane.det ∧
      (∃ e : Fin 2 → GaussQ, e ≠ 0 ∧ hf (conj ℚ GaussQ).toRingHom hypPlane e e = 0) ∧
      IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AE ℚ GaussQ) ∧
      Kg ⊆ SU (sigA (conj ℚ GaussQ)) (hypPlane.map (inclA ℚ GaussQ)) ∧ 1 ∈ Kg ∧
      (∀ a ∈ Kg, ∀ b ∈ Kg, a * b ∈ Kg) ∧ (∀ a ∈ Kg, a⁻¹ ∈ Kg) ∧
      (∃ O, IsOpen O ∧ O ∩ SU (sigA (conj ℚ GaussQ)) (hypPlane.map (inclA ℚ GaussQ)) = Kg) ∧
      gA ∈ SU (sigA (conj ℚ GaussQ)) (hypPlane.map (inclA ℚ GaussQ)) :=
  ⟨gauss_finrank, gauss_conj_ne_one, hypPlane_herm, hypPlane_unit, gauss_isotropic,
    isModuleTopology_AE, le_rfl, one_mem_SU, fun _ ha _ hb => mul_mem_SU ha hb,
    fun _ ha => inv_mem_SU _ _ ha, ⟨Set.univ, isOpen_univ, Set.univ_inter _⟩, gA_mem_SU⟩
end SAOpenHolds
end GroundTheory.Heights₂.Heights.StrongApprox
