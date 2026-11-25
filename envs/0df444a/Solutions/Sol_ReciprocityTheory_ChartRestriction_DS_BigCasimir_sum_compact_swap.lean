-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.BigCasimir.sum_compact_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:11:03.341103+00:00
-- url     : https://prove2.me/submissions/b4739191-08aa-447f-a917-7dcd6db6255f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA

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
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS.BigCasimir
theorem _root_.solution {R : Type*} [AddCommMonoid R] (f : Fin n → Fin n → R) :
    ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), f a b =
      ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), f b a := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [eq_comm]
end ReciprocityTheory.ChartRestriction.DS.BigCasimir
