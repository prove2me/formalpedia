-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.KRep.op_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:12.605287+00:00
-- url     : https://prove2.me/submissions/ffef41e9-f9c5-4f8a-9305-20c301994686

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Stable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_KRep_op_curve
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_KType_op_curve
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exists_curve
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exists_log
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
namespace KRep
theorem _root_.solution {ε : Fin n → Bool} (R : KRep ε) (k : KG ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ R.op k = NormedSpace.exp (R.dτ Y) := by
  obtain ⟨Y, hY, hk⟩ := exists_log ε k
  obtain ⟨γ, hγ⟩ := exists_curve ε hY
  have h1 : γ 1 = k := by
    apply onep_KG_ext
    rw [hγ 1, hk, Complex.ofReal_one, one_smul]
  refine ⟨Y, hY, ?_⟩
  rw [← h1, R.op_curve hY γ hγ 1, Complex.ofReal_one, one_smul]
end KRep
end ReciprocityTheory.ChartRestriction.DS.HW
