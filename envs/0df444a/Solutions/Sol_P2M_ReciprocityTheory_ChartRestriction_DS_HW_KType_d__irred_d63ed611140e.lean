-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_d__irred_d63ed611140e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:02:32.851608+00:00
-- url     : https://prove2.me/submissions/acc92e7f-13d6-40fb-9366-8e6371aa4285

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_inK_entry_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exp_mem_of_stable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_KType_op_eq_exp


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
theorem _root_.solution {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (W : Submodule ℂ T.V)
    (hW : ∀ a b, ε a = ε b → ∀ v ∈ W, T.dτ (Matrix.single a b 1) v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hstab : ∀ Y, inK ε Y → ∀ v ∈ W, T.dτ Y v ∈ W := by
    intro Y hY v hv
    rw [Matrix.matrix_eq_sum_single Y, map_sum, ContinuousLinearMap.sum_apply]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hab : ε a = ε b
    · have hs : Matrix.single a b (Y a b) = Y a b • Matrix.single a b (1 : ℂ) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [hs, map_smul, ContinuousLinearMap.smul_apply]
      exact W.smul_mem _ (hW a b hab v hv)
    · simp [inK_entry_eq_zero hY hab]
  refine T.irred W fun k v hv => ?_
  obtain ⟨Y, hY, hop⟩ := ReciprocityTheory.ChartRestriction.DS.HW.KType.op_eq_exp T k
  change T.op k v ∈ W
  rw [hop]
  exact exp_mem_of_stable W (T.dτ Y) (hstab Y hY) v hv
end KType
end ReciprocityTheory.ChartRestriction.DS.HW
