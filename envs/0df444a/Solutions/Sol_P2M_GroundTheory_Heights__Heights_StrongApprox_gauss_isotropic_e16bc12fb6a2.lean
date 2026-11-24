-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_gauss_isotropic_e16bc12fb6a2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:44.149843+00:00
-- url     : https://prove2.me/submissions/719470ac-5ed7-403e-8ff4-735c133b0157

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_LocGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_DenseRangeFiniteAdele
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
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
namespace GroundTheory.Heights₂.Heights.StrongApprox
theorem _root_.solution : ∃ e : Fin 2 → GaussQ, e ≠ 0 ∧ hf (conj ℚ GaussQ).toRingHom hypPlane e e = 0 :=
  ⟨e0, isotropic_vector_ne_zero, hf_e0e0⟩
end GroundTheory.Heights₂.Heights.StrongApprox
