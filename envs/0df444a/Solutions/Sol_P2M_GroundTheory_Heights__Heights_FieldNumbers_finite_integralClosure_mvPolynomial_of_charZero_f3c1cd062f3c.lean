-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_mvPolynomial_of_charZero_f3c1cd062f3c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:06:08.155804+00:00
-- url     : https://prove2.me/submissions/ef027d80-7b61-44c4-81ab-40ef31240dd2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_NoetherReduction
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_mvPolynomial_of_isSeparable_f40b322046a9

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
theorem _root_.solution (k : Type u) [Field k] [CharZero k]
    (s : ℕ) (L : Type u) [Field L] [Algebra (FractionRing (MvPolynomial (Fin s) k)) L]
    [FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) L]
    [Algebra (MvPolynomial (Fin s) k) L]
    [IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L] :
    Module.Finite (MvPolynomial (Fin s) k) (integralClosure (MvPolynomial (Fin s) k) L) := by
  have : CharZero (FractionRing (MvPolynomial (Fin s) k)) :=
    (RingHom.charZero_iff ((algebraMap (MvPolynomial (Fin s) k)
      (FractionRing (MvPolynomial (Fin s) k))).comp (algebraMap k (MvPolynomial (Fin s) k))).injective).mp
      inferInstance
  exact finite_integralClosure_mvPolynomial_of_isSeparable k s L
end GroundTheory.Heights₂.Heights.FieldNumbers
