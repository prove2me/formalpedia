-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_gA_mem_SU_40ec3b5d6c7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:56:06.225808+00:00
-- url     : https://prove2.me/submissions/906503e3-7f43-4db8-aa20-10ffd302a769

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_LocGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_DenseRangeFiniteAdele
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_conj_gI_dd63bad21afa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_sigA_invol_a7260028bf49
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_sigA_inclA_87fddbe307ad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_hypPlane_herm_A_b95d9f1393b9
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eichAlong_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_zero_left
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
theorem _root_.solution : gA ∈ SU (sigA (conj ℚ GaussQ)) (hypPlane.map (inclA ℚ GaussQ)) := by
  refine eichAlong_sub (f := inclA ℚ GaussQ ∘ f0) (fun x => sigA_invol x) hypPlane_herm_A
    (by simp [hf, hypPlane, e0, Fin.sum_univ_two]) ⟨0, inclA ℚ GaussQ gI, hf_zero_left _ _ _,
      hf_zero_left _ _ _, ?_, rfl⟩
  rw [hf_zero_left, sigA_inclA, conj_gI, map_neg]; ring
end GroundTheory.Heights₂.Heights.StrongApprox
