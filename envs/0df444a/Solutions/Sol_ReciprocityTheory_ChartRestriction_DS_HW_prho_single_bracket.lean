-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.prho_single_bracket
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:12:12.660136+00:00
-- url     : https://prove2.me/submissions/03768b1f-d677-4657-8b75-0b233b863701

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Unique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_PrhoEntryHasDerivAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open scoped Kronecker
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
variable {ε : Fin n → Bool} {β : Bool}
variable (ε β)
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (a b c d : Fin n) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1 h2; simp [Matrix.single_mul_single_same]
  · subst h1; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h2]
  · subst h2; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h1]
  · simp [Matrix.single_mul_single_of_ne, h1, h2]
end ReciprocityTheory.ChartRestriction.DS.HW
