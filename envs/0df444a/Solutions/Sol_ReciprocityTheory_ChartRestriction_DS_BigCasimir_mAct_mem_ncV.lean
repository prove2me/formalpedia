-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.BigCasimir.mAct_mem_ncV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:09:23.118676+00:00
-- url     : https://prove2.me/submissions/a5a8ebe5-e758-44cc-b6b4-7aa4a735d5e0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_mAct_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_mem_ncV_iff

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.BigCasimir
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS.BigCasimir
theorem _root_.solution (hV : IsKStableSub ε E V) (k : ℕ) {a b : Fin n} (hab : ε a = ε b)
    {F : Big n k M} (hF : F ∈ ncV ε V k) : mAct E k a b F ∈ ncV ε V k := by
  rw [mem_ncV_iff] at hF ⊢
  intro κ
  simp only [mAct_apply]
  exact ⟨fun h => hV a b hab _ ((hF κ).1 h), fun h => by rw [(hF κ).2 h, map_zero]⟩
end ReciprocityTheory.ChartRestriction.DS.BigCasimir
