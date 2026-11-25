-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.kexp_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:21:35.093201+00:00
-- url     : https://prove2.me/submissions/e3a1b0aa-1a0b-4660-87c2-d1aca29d6aec

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_toMK_facts

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
variable {ε : Fin n → Bool}
open PolarDecomposition
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hH : Xᴴ = X) :
    (toMK k * NormedSpace.exp X)ᴴ * (toMK k * NormedSpace.exp X) = NormedSpace.exp (X + X) := by
  rw [Matrix.conjTranspose_mul, ← Matrix.exp_conjTranspose, hH, mul_assoc, ← mul_assoc (toMK k)ᴴ,
    (toMK_facts k).1, one_mul, ← Matrix.exp_add_of_commute _ _ (Commute.refl _)]
end ReciprocityTheory.ChartRestriction.DS.S7
