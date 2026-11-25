-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casimir_apply_eq_casimirK_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:40.558898+00:00
-- url     : https://prove2.me/submissions/a6ce6f62-84f8-4a2f-bb1c-941caf50024e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_WeightBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_NcBound

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
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (x : M) :
    casimir E x = casimirK ε E x +
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), E a b (E b a x) := by
  simp only [casimir, casimirK, LinearMap.sum_apply, Module.End.mul_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun b => ε b = ε a)]
  congr 1
  refine Finset.sum_congr (Finset.filter_congr fun b _ => ?_) fun _ _ => rfl
  exact ⟨fun h h' => h h'.symm, fun h h' => h h'.symm⟩
end ReciprocityTheory.ChartRestriction.DS
