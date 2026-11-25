-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.wordContraction_prepend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:26:22.472957+00:00
-- url     : https://prove2.me/submissions/6ea6cf7b-e5cc-4d37-8680-c36a9bcb4921

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_wordContraction_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rootWordProduct_cons

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
theorem _root_.solution {k : ℕ} (p : Fin n × Fin n) (G : Big n k M) :
    phi E (k + 1) (indexPairPrepend p G) = E p.1 p.2 (phi E k G) := by
  rw [wordContraction_apply, wordContraction_apply, map_sum]
  have hL : ∀ κ : Fin (k + 1) → Fin n × Fin n, word E κ ((indexPairPrepend p G) κ) =
      if κ 0 = p then word E κ (G (Fin.tail κ)) else 0 := by
    intro κ
    show word E κ (if κ 0 = p then G (Fin.tail κ) else 0) = _
    split_ifs <;> simp
  simp_rw [hL]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun κ => Fin.tail κ) (fun κ' => Fin.cons p κ') ?_ ?_ ?_ ?_ ?_ <;>
  intro κ hκ <;>
  simp only [Finset.mem_coe, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter,
    Finset.mem_univ, true_and] at hκ ⊢
  · simp
  · rw [← hκ]; exact Fin.cons_self_tail κ
  · exact Fin.tail_cons _ _
  · have e : κ = Fin.cons p (Fin.tail κ) := by
      rw [← hκ]; exact (Fin.cons_self_tail κ).symm
    calc word E κ (G (Fin.tail κ))
        = word E (Fin.cons p (Fin.tail κ) : Fin (k + 1) → Fin n × Fin n) (G (Fin.tail κ)) := by
          rw [← e]
      _ = _ := by rw [rootWordProduct_cons]; rfl
end ReciprocityTheory.ChartRestriction.DS
