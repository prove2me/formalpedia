-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.sum_ite_update_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:26:22.672752+00:00
-- url     : https://prove2.me/submissions/812d311c-d14b-48bd-9ad1-c57a37c90b18

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule

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
theorem _root_.solution {k : ℕ} (i : Fin k) (P Q : Fin n × Fin n → Prop) [DecidablePred P]
    [DecidablePred Q] (f g : Fin n × Fin n → Fin n × Fin n) (hf : ∀ p, P p → Q (f p))
    (hg : ∀ p, Q p → P (g p)) (hgf : ∀ p, P p → g (f p) = p) (hfg : ∀ p, Q p → f (g p) = p)
    (W : (Fin k → Fin n × Fin n) → Module.End ℂ M) (F : Big n k M) :
    ∑ κ, (if P (κ i) then W κ (F (Function.update κ i (f (κ i)))) else 0) =
      ∑ κ, (if Q (κ i) then W (Function.update κ i (g (κ i))) (F κ) else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun κ => Function.update κ i (f (κ i)))
    (fun κ => Function.update κ i (g (κ i))) ?_ ?_ ?_ ?_ ?_ <;>
  intro κ hκ <;>
  simp only [Finset.mem_coe, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter,
    Finset.mem_univ, true_and] at hκ ⊢
  · simpa using hf _ hκ
  · simpa using hg _ hκ
  · simp [hgf _ hκ]
  · simp [hfg _ hκ]
  · simp [hgf _ hκ]
end ReciprocityTheory.ChartRestriction.DS
