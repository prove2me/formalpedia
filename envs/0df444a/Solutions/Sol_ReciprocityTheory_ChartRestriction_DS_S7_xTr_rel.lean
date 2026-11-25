-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.xTr_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:58:07.765088+00:00
-- url     : https://prove2.me/submissions/e3d312dc-4864-408e-adce-aaa53cd90c38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsOfFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhiA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_single_mul_single_one

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
theorem _root_.solution (a b c d : Fin n) : xTr n c d * xTr n a b - xTr n a b * xTr n c d =
    (if b = c then xTr n a d else 0) - (if d = a then xTr n c b else 0) := by
  unfold xTr
  rw [single_mul_single_one, single_mul_single_one]
  by_cases h1 : b = c
  · subst h1
    by_cases h2 : d = a
    · subst h2
      simp <;> abel
    · simp [h2, Ne.symm h2]
  · by_cases h2 : d = a
    · subst h2
      simp [h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]
end ReciprocityTheory.ChartRestriction.DS.S7
