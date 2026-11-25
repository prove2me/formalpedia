-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_mvPolynomial_of_isSeparable_f40b322046a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:48.367805+00:00
-- url     : https://prove2.me/submissions/bf5d6d1d-557e-453e-a387-a421795abd65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_NoetherReduction

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
theorem _root_.solution (k : Type u) [Field k] (s : ℕ)
    (L : Type u) [Field L] [Algebra (FractionRing (MvPolynomial (Fin s) k)) L]
    [FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) L]
    [Algebra.IsSeparable (FractionRing (MvPolynomial (Fin s) k)) L]
    [Algebra (MvPolynomial (Fin s) k) L]
    [IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L] :
    Module.Finite (MvPolynomial (Fin s) k) (integralClosure (MvPolynomial (Fin s) k) L) :=
  IsIntegralClosure.finite (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L
    (integralClosure (MvPolynomial (Fin s) k) L)
end GroundTheory.Heights₂.Heights.FieldNumbers
