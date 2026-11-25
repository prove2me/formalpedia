-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.commutator_rootWordProduct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:25.306513+00:00
-- url     : https://prove2.me/submissions/73f4b46b-dfaa-4e7c-95be-8acaf2ac03eb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rootWordProduct_zero
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
theorem _root_.solution (hE : IsGlRep E) (a b : Fin n) : ∀ {k : ℕ} (κ : Fin k → Fin n × Fin n),
    E a b * word E κ - word E κ * E a b =
      ∑ i, ((if (κ i).1 = b then word E (Function.update κ i (a, (κ i).2)) else 0) -
        (if (κ i).2 = a then word E (Function.update κ i ((κ i).1, b)) else 0))
  | 0, κ => by simp [rootWordProduct_zero]
  | k + 1, κ => by
    refine Fin.consCases (fun p τ => ?_) κ
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero, ← Fin.cons_update,
      rootWordProduct_cons]
    have ih := solution hE a b τ
    have h0 := hE a b p.1 p.2
    have hsplit : E a b * (E p.1 p.2 * word E τ) - E p.1 p.2 * word E τ * E a b =
        (E a b * E p.1 p.2 - E p.1 p.2 * E a b) * word E τ +
          E p.1 p.2 * (E a b * word E τ - word E τ * E a b) := by noncomm_ring
    rw [hsplit, h0, ih, Finset.mul_sum]
    congr 1
    · have e1 : (b = p.1) = (p.1 = b) := propext eq_comm
      simp only [e1]
      split_ifs <;> simp [sub_mul]
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp [mul_sub]
end ReciprocityTheory.ChartRestriction.DS
