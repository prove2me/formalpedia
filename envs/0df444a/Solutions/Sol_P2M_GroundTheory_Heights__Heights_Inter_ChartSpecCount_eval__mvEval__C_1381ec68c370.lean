-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartSpecCount_eval__mvEval__C_1381ec68c370
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:14:04.372089+00:00
-- url     : https://prove2.me/submissions/536bd5ae-3bf3-40bb-9ad3-7d351b7dbe17

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
theorem _root_.solution {A K Q : Type*} [CommRing A] [CommRing K] (k : A →+* K) (x : K) (G : Q → A[X])
    (F : MvPolynomial Q A) :
    (MvPolynomial.eval₂ C G F).eval₂ k x = MvPolynomial.eval₂ k (fun q => (G q).eval₂ k x) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add F G' hF hG => simp [Polynomial.eval₂_add, hF, hG]
  | mul_X F i hF => simp [Polynomial.eval₂_mul, hF]
end GroundTheory.Heights₂.Heights.Inter.ChartSpecCount
