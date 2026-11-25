-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.factorCasimir_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:42:39.62054+00:00
-- url     : https://prove2.me/submissions/85e0a70c-c718-4e56-b690-71e722242b14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCas
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_factorAd_adjoint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_factorAd_adjoint


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
theorem _root_.solution (k : ℕ) (F : Big n k M) :
    0 ≤ RCLike.re (inner ℂ (factorCasimir (M := M) ε k F) F) := by
  have hadj : ∀ (a b : Fin n) (X Y : Big n k M),
      inner ℂ ((∑ i, factorAd (M := M) k i a b) X) Y =
        inner ℂ X ((∑ i, factorAd (M := M) k i b a) Y) := by
    intro a b X Y
    simp only [LinearMap.sum_apply, sum_inner, inner_sum, factorAd_adjoint]
  unfold factorCasimir casimirK
  beta_reduce
  rw [LinearMap.sum_apply, sum_inner, map_sum]
  refine Finset.sum_nonneg fun a _ => ?_
  rw [LinearMap.sum_apply, sum_inner, map_sum]
  refine Finset.sum_nonneg fun b _ => ?_
  rw [Module.End.mul_apply, hadj]
  exact inner_self_nonneg
end ReciprocityTheory.ChartRestriction.DS
