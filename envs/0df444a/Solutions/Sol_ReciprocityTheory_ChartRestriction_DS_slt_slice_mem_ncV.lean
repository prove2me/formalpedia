-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slt_slice_mem_ncV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:25:48.062425+00:00
-- url     : https://prove2.me/submissions/144c90a9-3b3d-4647-adcc-c60131ecaa8e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SltEqZeroOfCompact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slt_mem_ncV_iff

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
theorem _root_.solution {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) {F : Big n k M}
    (hF : F ∈ ncV ε V k) : slice i κ F ∈ ncV ε V 1 := by
  rw [slt_mem_ncV_iff] at hF ⊢
  intro ι
  have h := hF (Function.update κ i (ι 0))
  change F (Function.update κ i (ι 0)) ∈ _
  by_cases c : ∀ j : Fin 1, ε (ι j).1 ≠ ε (ι j).2
  · rw [if_pos c]
    split_ifs at h with c'
    · exact h
    · rw [Submodule.mem_bot] at h
      rw [h]
      exact V.zero_mem
  · rw [if_neg c]
    have c' : ¬ ∀ j, ε ((Function.update κ i (ι 0)) j).1 ≠ ε ((Function.update κ i (ι 0)) j).2 := by
      intro hall
      apply c
      intro j
      have hj := hall i
      rw [Function.update_self] at hj
      rwa [Subsingleton.elim j 0]
    rwa [if_neg c'] at h
end ReciprocityTheory.ChartRestriction.DS
