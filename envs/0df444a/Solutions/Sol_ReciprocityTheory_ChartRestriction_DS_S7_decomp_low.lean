-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.decomp_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:15:12.07159+00:00
-- url     : https://prove2.me/submissions/4256edf1-e69b-4d04-9fed-18c8fcce20ca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_TauPart

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
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (B : Matrix (Fin n) (Fin n) ℂ) :
    B = -lowMinusUp B + (2 : ℂ) • lowPart B + diagPart B := by
  ext a b
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, lowMinusUp, lowPart, diagPart,
    Matrix.of_apply, Matrix.diagonal_apply, smul_eq_mul]
  rcases lt_trichotomy a b with h | rfl | h
  · rw [if_neg (lt_asymm h), if_pos h, if_neg (lt_asymm h), if_neg h.ne]
    ring
  · simp
  · rw [if_pos h, if_pos h, if_neg h.ne']
    ring
end ReciprocityTheory.ChartRestriction.DS.S7
