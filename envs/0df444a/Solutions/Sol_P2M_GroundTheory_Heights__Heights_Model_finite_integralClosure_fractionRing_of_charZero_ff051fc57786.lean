-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_fractionRing_of_charZero_ff051fc57786
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:56.999086+00:00
-- url     : https://prove2.me/submissions/54910a6d-87ea-4805-88bb-47fd092e7a2d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_of_isMaximal_e0c1554fd021
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_module_finite_of_forall_isMaximal_5580b993f60a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped nonZeroDivisors
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution
    (A : Type*) [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] :
    Module.Finite A (integralClosure A K) :=
  module_finite_of_forall_isMaximal fun 𝔪 _ => exists_pow_smul_mem_of_isMaximal A K 𝔪
end GroundTheory.Heights₂.Heights.Model
