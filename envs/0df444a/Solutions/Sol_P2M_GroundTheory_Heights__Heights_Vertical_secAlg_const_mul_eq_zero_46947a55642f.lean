-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_secAlg_const_mul_eq_zero_46947a55642f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:49:55.667027+00:00
-- url     : https://prove2.me/submissions/c81200ab-c92b-465a-b3ce-8fbee3604b0c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBTorsionFree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_eq_zero_of_secCoord_pow_mul_277c229bec77
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_chart_pow_mul_eq_zero_30c9ede0b670

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {D : Type*} [CommRing D] [IsDomain D] {n : ℕ} (e : ℕ) (R : Type*)
    [CommRing R] [Algebra (MvPolynomial (Par e n) D) R] (Q : Ideal (MvPolynomial (Fin n) D)) [Q.IsPrime]
    (S : Submonoid (MvPolynomial (Par e n) D)) [IsLocalization S R] (hQ : ∀ c : D, C c ∈ Q → c = 0)
    (QR : Ideal (MvPolynomial (Fin n) R)) (hQR : QR = chartModel e R Q) (y : Par e n → R)
    (hy : y = chartPar D e R) (c : D) (hc : c ≠ 0) (b : SecAlg QR y)
    (hb : algebraMap R _ (algebraMap (MvPolynomial (Par e n) D) R (C c)) * b = 0) : b = 0 := by
  subst hQR hy
  exact eq_zero_of_secCoord_pow_mul _ _ b fun j => chart_pow_mul_eq_zero e R Q j S hQ c hc b hb
end GroundTheory.Heights₂.Heights.Vertical
