-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.re_inner_casimir_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:42:56.464544+00:00
-- url     : https://prove2.me/submissions/0e2fd12e-fda5-4f7e-b6ea-610c5894fe99

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_WeightBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_NcBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimir_apply_eq_casimirK_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sum_nc_swap

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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M}
    (hU : IsInfUnitary ε E) (x : M) :
    RCLike.re (inner ℂ (casimir E x) x) = RCLike.re (inner ℂ (casimirK ε E x) x) -
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 := by
  rw [casimir_apply_eq_casimirK_add ε E x, inner_add_left, map_add, sum_inner, map_sum]
  have key : ∀ a, RCLike.re (inner ℂ (∑ b ∈ univ.filter (fun b => ε a ≠ ε b), E a b (E b a x)) x) =
      -∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E b a x‖ ^ 2 := by
    intro a
    rw [sum_inner, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hab : ε a ≠ ε b := (Finset.mem_filter.1 hb).2
    rw [hU a b (E b a x) x, adjSign, if_neg hab, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  simp only [key, Finset.sum_neg_distrib]
  rw [sum_nc_swap ε (fun a b => ‖E a b x‖ ^ 2)]
  ring
end ReciprocityTheory.ChartRestriction.DS
