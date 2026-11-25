-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_conj_gI_dd63bad21afa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:02:46.8068+00:00
-- url     : https://prove2.me/submissions/a115a9e5-1776-41c8-a20e-595623cd9cdb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_LocGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_DenseRangeFiniteAdele
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_conj_gaussQ_78f9ca11f54a
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
namespace GroundTheory.Heights₂.Heights.StrongApprox
theorem _root_.solution : conj ℚ GaussQ gI = -gI := by
  rw [conj_gaussQ]; ext <;> simp [gI]
end GroundTheory.Heights₂.Heights.StrongApprox
