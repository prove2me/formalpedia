-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.resSeries_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:31:16.669215+00:00
-- url     : https://prove2.me/submissions/ca44815f-2907-4ce1-8b6c-d202b6be4e92

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_prod_one_add_eq_of_resolvent

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
theorem _root_.solution {n : ℕ} {a : Fin n → ℂ} (ha : Function.Injective a) :
    resSeries a = ∑ s, (∏ s' ∈ univ.erase s, (a s - a s' + 1) / (a s - a s')) •
      (PowerSeries.X * (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹) := by
  have hP : ∀ s, PowerSeries.constantCoeff (1 - PowerSeries.C (a s) * PowerSeries.X) ≠ 0 := by
    intro s; simp
  have h := prod_one_add_eq_of_resolvent (Finset.univ : Finset (Fin n)) (PowerSeries ℂ) a ha.injOn
    (fun s => PowerSeries.X * (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹) (fun s _ t _ _ => by
      have key : (1 - PowerSeries.C (a t) * PowerSeries.X)⁻¹ - (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹ =
          (1 - PowerSeries.C (a t) * PowerSeries.X)⁻¹ * (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹ *
            ((1 - PowerSeries.C (a s) * PowerSeries.X) - (1 - PowerSeries.C (a t) * PowerSeries.X)) := by
        rw [mul_sub, mul_assoc, PowerSeries.inv_mul_cancel _ (hP s), mul_one,
          mul_comm ((1 - PowerSeries.C (a t) * PowerSeries.X)⁻¹), mul_assoc,
          PowerSeries.inv_mul_cancel _ (hP t), mul_one]
      rw [← mul_sub, key, PowerSeries.smul_eq_C_mul, map_sub]
      ring)
  rw [resSeries, h, add_sub_cancel_left]
end ReciprocityTheory.ChartRestriction.DS
