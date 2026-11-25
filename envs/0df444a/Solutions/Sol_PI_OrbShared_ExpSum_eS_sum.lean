-- Prove2me | solution 1 for PI.OrbShared.ExpSum.eS_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:20:05.613939+00:00
-- url     : https://prove2.me/submissions/ea38e90d-4a7f-4fe8-818b-82980561242c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_ExpSum
import Theorems.Thm_PI_OrbShared_ExpSum_eS_add
import Theorems.Thm_PI_OrbShared_ExpSum_eS_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.OrbShared PI.OrbShared.ExpSum
open MvPowerSeries
variable {K : Type*} [Field K] [CharZero K]
variable {τ υ : Type*}
namespace PI.OrbShared.ExpSum
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries τ K)
    (hf : ∀ i ∈ s, constantCoeff (f i) = 0) : eS (∑ i ∈ s, f i) = ∏ i ∈ s, eS (f i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.sum_empty, Finset.prod_empty]
    exact eS_zero
  | @insert a s ha ih =>
    intro hf
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      eS_add _ _ (hf a (Finset.mem_insert_self a s)) ?_,
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]
    rw [map_sum]
    exact Finset.sum_eq_zero fun i hi => hf i (Finset.mem_insert_of_mem hi)
end PI.OrbShared.ExpSum
