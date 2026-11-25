-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall.eval_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:01:05.787168+00:00
-- url     : https://prove2.me/submissions/a3cd4f3b-1b33-4b86-b35b-fdc2fe917630

import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsTorusPointOneLeNormSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_UnitPointLiftBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall
open MvPolynomial ReciprocityTheory.MultiplicativeHeights
variable {K : Type*} [NormedField K] [IsUltrametricDist K] {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall
theorem _root_.solution (PO : MvPolynomial ι (unitBallRing K)) (σ : ι → unitBallRing K) :
    eval (fun i => (σ i : K)) (MvPolynomial.map (unitBallRing K).subtype PO) =
      ((eval σ PO : unitBallRing K) : K) := by
  induction PO using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.UnitPointLiftBall
