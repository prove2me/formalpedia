-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_HW_KRep_stable_of_d__stable_939501e86c53
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:33.223461+00:00
-- url     : https://prove2.me/submissions/ab8f3285-2035-4cd4-8ad6-e57927f10592

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Stable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_KRep_op_eq_exp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_KType_op_eq_exp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exp_mem_of_stable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_inK_entry_eq_zero


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
theorem _root_.solution {ε : Fin n → Bool} (R : KRep ε) (W : Submodule ℂ R.V)
    (hW : ∀ a b, ε a = ε b → ∀ v ∈ W, R.dτ (Matrix.single a b 1) v ∈ W) :
    ∀ k : KG ε, ∀ v ∈ W, R.op k v ∈ W := by
  intro k v hv
  obtain ⟨Y, hY, hk⟩ := R.op_eq_exp k
  rw [hk]
  refine exp_mem_of_stable W (R.dτ Y) ?_ v hv
  intro w hw
  rw [Matrix.matrix_eq_sum_single Y]
  simp only [map_sum, FunLike.coe_sum, Finset.sum_apply]
  refine W.sum_mem fun a _ => W.sum_mem fun b _ => ?_
  by_cases hab : ε a = ε b
  · rw [show Matrix.single a b (Y a b) = Y a b • Matrix.single a b 1 by
        rw [Matrix.smul_single, smul_eq_mul, mul_one],
      map_smul, _root_.smul_apply]
    exact W.smul_mem _ (hW a b hab w hw)
  · rw [inK_entry_eq_zero hY hab, Matrix.single_zero, map_zero]
    exact W.zero_mem
end KRep
end ReciprocityTheory.ChartRestriction.DS.HW
