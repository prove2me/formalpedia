-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.lowest_k_type_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:24:55.232678+00:00
-- url     : https://prove2.me/submissions/f29f10eb-0dc6-4d3c-af48-c11d45201570

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HcParamGapGeIndex
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_lowK_card_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_lowK_card_lt

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
theorem _root_.solution (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    lowK ε lam a = lam a + ((n : ℝ) - 1) / 2 - (a : ℕ)
      - ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ)
      + ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) := by
  have hg := lowK_card_gt ε a
  have hl := lowK_card_lt ε a
  have ha := a.isLt
  simp only [lowK, rhoN, rhoC, Pi.add_apply, Pi.sub_apply]
  set A1 := (univ.filter fun b => a < b ∧ ε b ≠ ε a).card
  set A2 := (univ.filter fun b => a < b ∧ ε b = ε a).card
  set A3 := (univ.filter fun b => b < a ∧ ε b ≠ ε a).card
  set A4 := (univ.filter fun b => b < a ∧ ε b = ε a).card
  have e1 : ((A1 : ℕ) : ℝ) + A2 + 1 + (a : ℕ) = n := by
    exact_mod_cast (show A1 + A2 + 1 + (a : ℕ) = n by omega)
  have e2 : ((A3 : ℕ) : ℝ) + A4 = (a : ℕ) := by exact_mod_cast hl
  linarith
end ReciprocityTheory.ChartRestriction.DS.HW
