-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_hyperbolicPlane_hermitian_at_five_95fc9fec3fa8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:20:39.658258+00:00
-- url     : https://prove2.me/submissions/e6138d8f-97fb-46b8-b4e3-d61e4a592d15

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
theorem _root_.solution : (hypPlane.map (inclV GaussQ v5))ᵀ =
    (hypPlane.map (inclV GaussQ v5)).map (sigV (conj ℚ GaussQ) v5).toRingHom := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hypPlane]
end GroundTheory.Heights₂.Heights.StrongApprox
