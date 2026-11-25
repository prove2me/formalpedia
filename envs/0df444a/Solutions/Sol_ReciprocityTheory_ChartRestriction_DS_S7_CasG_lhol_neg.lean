-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CasG.lhol_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:20:11.939232+00:00
-- url     : https://prove2.me/submissions/b16aec9f-b8e2-498d-b23a-26f2b84f8d03

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiMLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasLPsM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LholClmEventually

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CasG
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace ReciprocityTheory.ChartRestriction.DS.S7.CasG
theorem _root_.solution (X : Matrix (Fin n) (Fin n) ℂ) (G : Matrix (Fin n) (Fin n) ℂ → E)
    (z : Matrix (Fin n) (Fin n) ℂ) : Lhol X (fun w => -G w) z = -Lhol X G z := by
  unfold Lhol
  by_cases hG : DifferentiableAt ℂ G z
  · have h2 := hG.hasFDerivAt.neg.fderiv
    exact congrArg (fun A : Matrix (Fin n) (Fin n) ℂ →L[ℂ] E => A (X * z)) h2
  · have h3 : ¬ DifferentiableAt ℂ (fun w => -G w) z := fun h => hG (differentiableAt_neg_iff.1 h)
    simp [fderiv_zero_of_not_differentiableAt hG, fderiv_zero_of_not_differentiableAt h3]
end ReciprocityTheory.ChartRestriction.DS.S7.CasG
