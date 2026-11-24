-- Prove2me | solution 1 for P2M_GlobalTheory_FormalCalc_pderiv_subst__7084ce132710
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:49:42.633807+00:00
-- url     : https://prove2.me/submissions/4ae8462d-826c-42be-a80e-44185ed45077

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries Sum
variable {σ τ ι κ μ A : Type*} [CommRing A]
namespace GlobalTheory.FormalCalc
theorem _root_.solution [Fintype ι] {a : ι → MvPowerSeries κ A}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries ι A) (j : κ) :
    pderiv A j (subst a f) = ∑ i, subst a (pderiv A i f) * pderiv A j (a i) :=
  pderiv_subst (hasSubst_of_constantCoeff_zero ha) f j
end GlobalTheory.FormalCalc
