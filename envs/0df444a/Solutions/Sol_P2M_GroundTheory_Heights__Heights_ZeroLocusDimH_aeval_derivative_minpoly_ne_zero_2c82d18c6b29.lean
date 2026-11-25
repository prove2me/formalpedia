-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_aeval_derivative_minpoly_ne_zero_2c82d18c6b29
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:23.15187+00:00
-- url     : https://prove2.me/submissions/f589ffde-c15b-4212-9453-cc81a5315773

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ZeroLocusDimH
namespace GroundTheory.Heights₂.Heights.ZeroLocusDimH
theorem _root_.solution {R A : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CharZero R] [CommRing A] [IsDomain A] [Algebra R A]
    [Algebra.IsIntegral R A] (hinj : Function.Injective (algebraMap R A)) (x : A) :
    Polynomial.aeval x (Polynomial.derivative (minpoly R x)) ≠ 0 := by
  have : Module.IsTorsionFree R A := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  have hx : IsIntegral R x := Algebra.IsIntegral.isIntegral x
  intro h0
  have hdvd := minpoly.isIntegrallyClosed_dvd hx h0
  have hmon := minpoly.monic hx
  have hne : Polynomial.derivative (minpoly R x) ≠ 0 := by
    intro hd
    exact (minpoly.natDegree_pos hx).ne' (Polynomial.derivative_eq_zero.1 hd)
  have h1 := Polynomial.degree_le_of_dvd hdvd hne
  have h2 := Polynomial.degree_derivative_lt hmon.ne_zero
  exact absurd h1 (not_le.2 h2)
end GroundTheory.Heights₂.Heights.ZeroLocusDimH
