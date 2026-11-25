-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_unipotent_mem_specialUnitary_aa67ebe7e39c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:05:58.17359+00:00
-- url     : https://prove2.me/submissions/75afc2e3-b1d5-401d-9e53-39c40ba57b76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_LocGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_DenseRangeFiniteAdele
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_sigV_invol_0285d3393774
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_unipotent_mem_eichlerAlong_c441d5fa2cf2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_hyperbolicPlane_hermitian_at_five_95fc9fec3fa8
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eichAlong_sub
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
theorem _root_.solution : g5 ∈ SU (sigV (conj ℚ GaussQ) v5).toRingHom (hypPlane.map (inclV GaussQ v5)) :=
  eichAlong_sub (fun x => sigV_invol v5 x) hyperbolicPlane_hermitian_at_five
    (by simp [hf, hypPlane, e0, Fin.sum_univ_two]) unipotent_mem_eichlerAlong
end GroundTheory.Heights₂.Heights.StrongApprox
