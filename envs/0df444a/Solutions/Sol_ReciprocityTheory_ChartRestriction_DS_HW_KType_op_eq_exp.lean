-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.KType.op_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:39:38.444411+00:00
-- url     : https://prove2.me/submissions/42339e83-9f0b-4ec9-9de5-a7e7357b0501

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exists_log
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_KType_op_curve
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exists_curve
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_onep_KG_ext


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
namespace KType
theorem _root_.solution {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ T.op k = NormedSpace.exp (T.dτ Y) := by
  obtain ⟨Y, hY, he⟩ := exists_log ε k
  obtain ⟨γ, hγ⟩ := exists_curve ε hY
  have h1 : γ 1 = k := onep_KG_ext (by rw [hγ, he]; simp)
  refine ⟨Y, hY, ?_⟩
  have h2 := ReciprocityTheory.ChartRestriction.DS.HW.KType.op_curve T hY γ hγ 1
  rw [h1] at h2
  simpa using h2
end KType
end ReciprocityTheory.ChartRestriction.DS.HW
