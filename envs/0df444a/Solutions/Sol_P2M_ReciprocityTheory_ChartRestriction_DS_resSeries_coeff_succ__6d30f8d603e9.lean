-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_resSeries_coeff_succ__6d30f8d603e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:35.206591+00:00
-- url     : https://prove2.me/submissions/41903369-6365-46b3-9506-fc636a2014a7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_inv_one_sub_C_mul_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_resSeries_eq_sum

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
theorem _root_.solution {n : ℕ} {a : Fin n → ℂ} (ha : Function.Injective a) (k : ℕ) :
    PowerSeries.coeff (k + 1) (resSeries a) =
      ∑ s, (∏ s' ∈ univ.erase s, (a s - a s' + 1) / (a s - a s')) * a s ^ k := by
  rw [resSeries_eq_sum ha, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [PowerSeries.coeff_smul, inv_one_sub_C_mul_X, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk,
    smul_eq_mul]
end ReciprocityTheory.ChartRestriction.DS
