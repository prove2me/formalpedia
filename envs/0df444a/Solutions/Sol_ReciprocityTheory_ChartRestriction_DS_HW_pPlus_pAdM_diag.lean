-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.pPlus_pAdM_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:26:44.072007+00:00
-- url     : https://prove2.me/submissions/a72527c3-da82-4db9-9188-e34d26bb2138

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Weight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_PPlusPWtInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pPlus_fst_ne_snd

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
theorem _root_.solution (ε : Fin n → Bool) (β : Bool) (a : Fin n) :
    pAdM ε β a a = Matrix.diagonal fun p => ((pWt ε β p a : ℝ) : ℂ) := by
  ext p q
  by_cases hpq : p = q
  · subst hpq
    simp only [pAdM, pWt, Pi.single_apply, Pi.sub_apply, Matrix.diagonal_apply_eq, and_true, and_self]
    by_cases h1 : p.1.1 = a <;> by_cases h2 : p.1.2 = a
    · exact absurd (h1.trans h2.symm) (pPlus_fst_ne_snd p)
    · rw [if_pos h1, if_neg h2, if_pos h1.symm, if_neg (Ne.symm h2)]; simp
    · rw [if_neg h1, if_pos h2, if_neg (Ne.symm h1), if_pos h2.symm]; simp
    · rw [if_neg h1, if_neg h2, if_neg (Ne.symm h1), if_neg (Ne.symm h2)]; simp
  · rw [Matrix.diagonal_apply_ne _ hpq]
    have h1 : ¬ (p.1.1 = a ∧ q.1.1 = a ∧ p.1.2 = q.1.2) := fun h =>
      hpq (Subtype.ext (Prod.ext (h.1.trans h.2.1.symm) h.2.2))
    have h2 : ¬ (q.1.2 = a ∧ p.1.2 = a ∧ p.1.1 = q.1.1) := fun h =>
      hpq (Subtype.ext (Prod.ext h.2.2 (h.2.1.trans h.1.symm)))
    simp only [pAdM, if_neg h1, if_neg h2, sub_self]
end ReciprocityTheory.ChartRestriction.DS.HW
