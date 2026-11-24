-- Prove2me | solution 1 for PI.QnHermHaar.commSumA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:54:11.321802+00:00
-- url     : https://prove2.me/submissions/5b57be41-71bd-4567-87e4-9734eece6028

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_LowerRightNeZeroOfUpperRightZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SumFourCommVersion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnHermHaar
theorem _root_.solution {A : Type*} [Ring A] {ι : Type*} [Fintype ι] (h : ι → A) (g : A) :
    (∑ i, h i) * g - g * (∑ i, h i) = ∑ i, (h i * g - g * h i) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
end PI.QnHermHaar
