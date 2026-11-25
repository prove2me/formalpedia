-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_add_e11f6d6b4fb2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:14:31.81269+00:00
-- url     : https://prove2.me/submissions/08ca4703-a590-45fe-b01a-89931a362df1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartHomog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (u : ∀ k, ι k) (a c : K → ℕ) :
    (chartMonomial u (a + c) : MRing ι F) = chartMonomial u a * chartMonomial u c := by
  simp only [chartMonomial, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
end GroundTheory.Heights₂.Heights.FieldNumbers
