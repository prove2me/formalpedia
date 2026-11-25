-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.wd_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:08.148719+00:00
-- url     : https://prove2.me/submissions/9e298625-8611-468f-9048-6343ece3c179

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_KhwLowKSubRootEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (a b : Fin n) :
    ((if wdP ε a b then (1:ℝ) else 0) - (if wdP ε b a then (1:ℝ) else 0)) =
    ((if a < b ∧ ε b = ε a then (1:ℝ) else 0) - (if b < a ∧ ε b = ε a then 1 else 0)) -
    ((if a < b ∧ ε b ≠ ε a then (1:ℝ) else 0) - (if b < a ∧ ε b ≠ ε a then 1 else 0)) := by
  unfold wdP
  rcases lt_trichotomy a b with h | rfl | h
  · by_cases he : ε a = ε b
    · simp [h, lt_asymm h, he]
    · simp [h, lt_asymm h, he, Ne.symm he]
  · simp
  · by_cases he : ε a = ε b
    · simp [h, lt_asymm h, he]
    · simp [h, lt_asymm h, he, Ne.symm he]
end ReciprocityTheory.ChartRestriction.DS
