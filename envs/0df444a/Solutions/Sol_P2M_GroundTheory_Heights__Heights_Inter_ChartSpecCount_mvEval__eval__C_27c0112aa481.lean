-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartSpecCount_mvEval__eval__C_27c0112aa481
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:14:07.21066+00:00
-- url     : https://prove2.me/submissions/2e1d1aeb-7e11-46b7-be8d-a6de84ca64a6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartPrimElt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocAwaySpec
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartSpecCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartSpecCount

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open Polynomial
open GroundTheory.Heights₂.Heights.Inter.ChartSpecCount
namespace GroundTheory.Heights₂.Heights.Inter.ChartSpecCount
theorem _root_.solution {A K Q : Type*} [CommRing A] [CommRing K] (k : A →+* K) (y : Q → K)
    (τ : MvPolynomial Q A) (p : A[X]) :
    MvPolynomial.eval₂ k y (p.eval₂ MvPolynomial.C τ) = p.eval₂ k (MvPolynomial.eval₂ k y τ) := by
  induction p using Polynomial.induction_on' with
  | add p p' hp hp' => simp [Polynomial.eval₂_add, hp, hp']
  | monomial n a => simp [Polynomial.eval₂_monomial]
end GroundTheory.Heights₂.Heights.Inter.ChartSpecCount
