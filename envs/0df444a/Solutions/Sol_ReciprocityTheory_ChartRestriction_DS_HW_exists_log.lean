-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.exists_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:20:40.635794+00:00
-- url     : https://prove2.me/submissions/e04686b0-f440-44cc-a580-2935b668da4e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Theorems.Thm_Formalism_REAL_kExp


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) (k : KG ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ toMK k = NormedSpace.exp Y := by
  have hk : toMK k ∈ Formalism.REAL.Kset ε := by
    rw [← Formalism.REAL.range_toMK]; exact ⟨k, rfl⟩
  obtain ⟨Y, hY, he, -⟩ := Formalism.REAL.kExp n ε (toMK k) hk
  exact ⟨Y, hY, he.symm⟩
end ReciprocityTheory.ChartRestriction.DS.HW
