-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_aeval_cons_eq_eval__finSuccEquiv_b773e260af41
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:12:05.419428+00:00
-- url     : https://prove2.me/submissions/252b0c2a-af6a-491a-9ddb-8333837ddfca

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
theorem _root_.solution {k : ℕ} {B : Type*} [CommRing B] [Algebra ℂ B] (b : B)
    (y : Fin k → B) (P : MvPolynomial (Fin (k + 1)) ℂ) :
    aeval (Fin.cons b y : Fin (k + 1) → B) P =
      Polynomial.eval₂ (aeval y).toRingHom b (finSuccEquiv ℂ k P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [← algebraMap_eq, AlgHom.commutes, AlgEquiv.commutes, Polynomial.algebraMap_apply,
      Polynomial.eval₂_C]
    exact ((aeval y).commutes a).symm
  | add p q hp hq => simp [hp, hq, Polynomial.eval₂_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, Polynomial.eval₂_mul, hp]
    congr 1
    cases i using Fin.cases with
    | zero => simp [finSuccEquiv_X_zero]
    | succ i => simp [finSuccEquiv_X_succ]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
