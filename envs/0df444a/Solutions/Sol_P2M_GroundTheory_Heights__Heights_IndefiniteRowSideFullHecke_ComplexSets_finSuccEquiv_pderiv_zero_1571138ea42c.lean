-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_finSuccEquiv_pderiv_zero_1571138ea42c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:12:07.293203+00:00
-- url     : https://prove2.me/submissions/71d2a555-1630-49dd-ad8d-661880d7a1eb

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjectionCoordinateEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjectionCoordinateEquation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {k : ℕ} (P : MvPolynomial (Fin (k + 1)) ℂ) :
    finSuccEquiv ℂ k (pderiv 0 P) = Polynomial.derivative (finSuccEquiv ℂ k P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [pderiv_C, map_zero, ← algebraMap_eq, AlgEquiv.commutes, Polynomial.algebraMap_apply,
      Polynomial.derivative_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hp, map_mul,
      Polynomial.derivative_mul]
    cases i using Fin.cases with
    | zero =>
      simp only [finSuccEquiv_X_zero, pderiv_X_self, map_one, Polynomial.derivative_X]
      ring
    | succ i =>
      simp only [finSuccEquiv_X_succ, pderiv_X, Pi.single_apply, Fin.succ_ne_zero, if_false, map_zero,
        Polynomial.derivative_C]
      ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
