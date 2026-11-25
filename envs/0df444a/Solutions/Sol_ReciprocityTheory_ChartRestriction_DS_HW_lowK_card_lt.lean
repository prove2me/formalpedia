-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.lowK_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:10:53.433188+00:00
-- url     : https://prove2.me/submissions/4e8830bc-f57b-4ea7-b1da-70094d453edb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HcParamGapGeIndex

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) (a : Fin n) :
    (univ.filter fun b => b < a ∧ ε b ≠ ε a).card + (univ.filter fun b => b < a ∧ ε b = ε a).card
      = a := by
  have key : ∀ s : Finset (Fin n), (s.filter (fun b => ε b ≠ ε a)).card +
      (s.filter (fun b => ¬ (ε b ≠ ε a))).card = s.card := by
    intro s
    first
    | exact Finset.card_filter_add_card_filter_not _
    | exact Finset.filter_card_add_filter_neg_card_eq_card _
    | rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_neg s s _),
        Finset.filter_union_filter_neg_eq]
    | rw [← Finset.card_disjoint_union (Finset.disjoint_filter_filter_neg s s _),
        Finset.filter_union_filter_neg_eq]
  rw [← Fin.card_Iio a, ← key (Finset.Iio a)]
  congr 1 <;> congr 1 <;> ext b <;> simp
end ReciprocityTheory.ChartRestriction.DS.HW
