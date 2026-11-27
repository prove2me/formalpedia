-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_of_charZero_501e3d5cc1e2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:55:06.04216+00:00
-- url     : https://prove2.me/submissions/0dcda494-8401-4f0c-be8c-357965d4c6d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_NoetherReduction
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_of_forall_mvPolynomial_4e8918a7d574
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_mvPolynomial_of_charZero_f3c1cd062f3c

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution
    (k A : Type u) [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] :
    Module.Finite A (integralClosure A L) :=
  finite_integralClosure_of_forall_mvPolynomial k A K L fun s L' _ _ _ _ _ =>
    finite_integralClosure_mvPolynomial_of_charZero k s L'
end GroundTheory.Heights₂.Heights.FieldNumbers
