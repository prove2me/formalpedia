-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_HypPairExists_hyps_7370eaa5e57f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:08:04.851065+00:00
-- url     : https://prove2.me/submissions/f674a056-25e8-41d6-9808-4c35d39119bc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_LocGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_DenseRangeFiniteAdele
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_gauss_invol_b290ae2f2fc0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_gauss_two_ne_zero_3418c98180a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_hypPlane_herm__a969c2c0434a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_hypPlane_unit_65a5a7802c0c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_isotropic_vector_ne_zero_7bfb4af349bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_hf_e0e0_6b9fc7c10d02

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
namespace HypPairExists
theorem _root_.solution :
    (∀ x, (conj ℚ GaussQ).toRingHom ((conj ℚ GaussQ).toRingHom x) = x) ∧ (2 : GaussQ) ≠ 0 ∧
      hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ).toRingHom ∧ IsUnit hypPlane.det ∧ e0 ≠ 0 ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 e0 = 0 :=
  ⟨gauss_invol, gauss_two_ne_zero, hypPlane_herm', hypPlane_unit, isotropic_vector_ne_zero, hf_e0e0⟩
end HypPairExists
end GroundTheory.Heights₂.Heights.StrongApprox
