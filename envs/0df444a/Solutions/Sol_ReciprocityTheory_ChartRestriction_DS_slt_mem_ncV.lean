-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slt_mem_ncV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:02:03.532241+00:00
-- url     : https://prove2.me/submissions/89756b9d-fbf4-4086-a9be-382e60c717d2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SltEqZeroOfCompact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slt_eq_slice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slt_big_one_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slt_slice_mem_ncV

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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {k : ℕ} (i : Fin k) (r : {j // j ≠ i} → Fin n × Fin n) {F : Big n k M}
    (hF : F ∈ ncV ε V k) : slt i r F ∈ ncV ε V 1 := by
  by_cases he : IsEmpty (Fin n × Fin n)
  · rw [slt_big_one_eq_zero he (slt i r F)]
    exact Submodule.zero_mem _
  · rw [not_isEmpty_iff] at he
    obtain ⟨p⟩ := he
    rw [slt_eq_slice i r p]
    exact slt_slice_mem_ncV i _ hF
end ReciprocityTheory.ChartRestriction.DS
