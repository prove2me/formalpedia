-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.kfa_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:15:09.391445+00:00
-- url     : https://prove2.me/submissions/a060f364-2faa-469c-b2eb-15b51a4e0a7f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFactsA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (s t : ℝ) :
    kfaKG ε hY (s + t) = kfaKG ε hY s * kfaKG ε hY t := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  show NormedSpace.exp (((s + t : ℝ) : ℂ) • Y) =
    NormedSpace.exp ((s : ℂ) • Y) * NormedSpace.exp ((t : ℂ) • Y)
  rw [Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _)
end ReciprocityTheory.ChartRestriction.DS.S7
