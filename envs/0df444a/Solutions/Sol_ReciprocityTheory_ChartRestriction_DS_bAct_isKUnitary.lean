-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.bAct_isKUnitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:41:42.891143+00:00
-- url     : https://prove2.me/submissions/ae5d5e55-d65b-46fc-b535-5520735468e8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mAct_apply
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
theorem _root_.solution (hU : IsInfUnitary ε E) (k : ℕ) : IsKUnitary ε (bAct E k) := by
  intro a b hab F G
  simp only [bAct, LinearMap.add_apply, LinearMap.sum_apply, inner_add_left, inner_add_right,
    sum_inner, inner_sum, factorAd_adjoint]
  congr 1
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [mAct_apply, mAct_apply, hU a b, adjSign, if_pos hab, one_mul]
end ReciprocityTheory.ChartRestriction.DS
