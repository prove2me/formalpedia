-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.positionPrepend_mem_noncompactPositionSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:25:03.93079+00:00
-- url     : https://prove2.me/submissions/192892cd-74ff-48e7-8522-1b4887af5f05

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_mem_noncompactPositionSubmodule_iff__607b2d11fea7

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
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {k : ℕ} {p : Fin n × Fin n} (hp : ε p.1 ≠ ε p.2) {G : Big n k M}
    (hG : G ∈ ncV ε V k) : indexPairPrepend p G ∈ ncV ε V (k + 1) := by
  rw [mem_noncompactPositionSubmodule_iff'] at hG ⊢
  intro κ
  by_cases h0 : κ 0 = p
  · have hv : (indexPairPrepend p G) κ = G (Fin.tail κ) := by
      show (if κ 0 = p then G (Fin.tail κ) else 0) = _
      rw [if_pos h0]
    rw [hv]
    have h := hG (Fin.tail κ)
    by_cases ht : ∀ i, ε (Fin.tail κ i).1 ≠ ε (Fin.tail κ i).2
    · rw [if_pos ht] at h
      have hk : ∀ i, ε (κ i).1 ≠ ε (κ i).2 := by
        intro i
        induction i using Fin.cases with
        | zero => rw [h0]; exact hp
        | succ j => exact ht j
      rw [if_pos hk]; exact h
    · rw [if_neg ht, Submodule.mem_bot] at h
      rw [h]; exact Submodule.zero_mem _
  · have hv : (indexPairPrepend p G) κ = 0 := by
      show (if κ 0 = p then G (Fin.tail κ) else 0) = _
      rw [if_neg h0]
    rw [hv]; exact Submodule.zero_mem _
end ReciprocityTheory.ChartRestriction.DS
