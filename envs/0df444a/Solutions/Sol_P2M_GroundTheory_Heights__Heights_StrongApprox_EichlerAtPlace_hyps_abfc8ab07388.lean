-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_hyps_abfc8ab07388
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:07:54.054189+00:00
-- url     : https://prove2.me/submissions/b4c05be2-d2bb-4482-9397-4fad6f08fd25

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_hf_e0e0_6b9fc7c10d02
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_hf_f0f0_a1dde18274c7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_hf_e0f0_88b2973874db
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_unipotent_mem_eichlerSet_7faf57259b7e

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
namespace EichlerAtPlace
theorem _root_.solution :
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧ hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ) ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 e0 = 0 ∧ hf (conj ℚ GaussQ).toRingHom hypPlane f0 f0 = 0 ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 f0 = 1 ∧
      g5 ∈ eichSet (sigV (conj ℚ GaussQ) v5).toRingHom (hypPlane.map (inclV GaussQ v5))
        (inclV GaussQ v5 ∘ e0) (inclV GaussQ v5 ∘ f0) :=
  ⟨gauss_finrank, gauss_conj_ne_one, hypPlane_herm, hf_e0e0, hf_f0f0, hf_e0f0, unipotent_mem_eichlerSet⟩
end EichlerAtPlace
end GroundTheory.Heights₂.Heights.StrongApprox
