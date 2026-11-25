-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefOp_kexp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:13.971803+00:00
-- url     : https://prove2.me/submissions/176af7f3-f955-42c7-926e-161c500364af

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CoefOp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefOp_unitary_mul_exp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_toMK_facts


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} (k : S7.KG ε) (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (S7.toMK k * NormedSpace.exp X)‖ ≤ Real.exp (Real.sqrt (S7.hs X)) := by
  have hk : S7.toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    exact (S7.toMK_facts k).2.1
  exact coefOp_unitary_mul_exp hk X
end ReciprocityTheory.ChartRestriction.DS
