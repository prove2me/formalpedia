-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.adDFull_bracket
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:34:11.300562+00:00
-- url     : https://prove2.me/submissions/9d8a3f4c-8490-4d60-91b1-392c752a78f3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Unique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_PrhoEntryHasDerivAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_prho_sub_kron
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_prho_kron_sub

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
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (X Y : Matrix (Fin n) (Fin n) ℂ) :
    adDFull X * adDFull Y - adDFull Y * adDFull X = adDFull (X * Y - Y * X) := by
  simp only [adDFull, sub_mul, mul_sub, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.transpose_sub, Matrix.transpose_mul, prho_sub_kron, prho_kron_sub]
  abel
end ReciprocityTheory.ChartRestriction.DS.HW
