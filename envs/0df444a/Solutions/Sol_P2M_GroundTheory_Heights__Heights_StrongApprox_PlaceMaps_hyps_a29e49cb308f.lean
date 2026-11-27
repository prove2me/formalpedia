-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_hyps_a29e49cb308f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:08:25.689817+00:00
-- url     : https://prove2.me/submissions/6ce3db35-2728-4ba9-86bc-de265032951c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_LocGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_DenseRangeFiniteAdele
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_place_three_ne_place_five_9f0c043ae38b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_gauss_finrank_b2407f5ee816
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_gauss_conj_ne_one_e84154cc7c34
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_unipotent_mem_specialUnitary_aa67ebe7e39c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_gA_mem_SU_40ec3b5d6c7a

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
namespace PlaceMaps
theorem _root_.solution :
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧ v3 ≠ v5 ∧
      g5 ∈ SU (sigV (conj ℚ GaussQ) v5).toRingHom (hypPlane.map (inclV GaussQ v5)) ∧
      gA ∈ SU (sigA (conj ℚ GaussQ)) (hypPlane.map (inclA ℚ GaussQ)) :=
  ⟨gauss_finrank, gauss_conj_ne_one, place_three_ne_place_five, unipotent_mem_specialUnitary, gA_mem_SU⟩
end PlaceMaps
end GroundTheory.Heights₂.Heights.StrongApprox
