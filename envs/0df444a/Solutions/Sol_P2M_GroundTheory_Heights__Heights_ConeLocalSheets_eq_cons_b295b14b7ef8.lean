-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeLocalSheets_eq_cons_b295b14b7ef8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:21.752824+00:00
-- url     : https://prove2.me/submissions/cafb2191-8cc4-47d3-a6e3-412608df6aa2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalSheets

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj mcPts fibre segre)
open Matrix
open GroundTheory.Heights₂.Heights.ConeLocalSheets
variable {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ConeLocalSheets
theorem _root_.solution {v : Fin (e + 1) → ℂ} {y : Fin e → ℂ} (h0 : v 0 = 1) (hs : ∀ i, v i.succ = y i) :
    v = Fin.cons 1 y := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [h0]
  · simp [hs]
end GroundTheory.Heights₂.Heights.ConeLocalSheets
