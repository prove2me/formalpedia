-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.csq_sum_univ_pm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:25.802318+00:00
-- url     : https://prove2.me/submissions/f61eb011-23a0-43a7-9950-dd6f3f3f142b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqA

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
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {R : Type*} [AddCommMonoid R] (ε : Fin n → Bool) (f : Fin n → R) :
    ∑ a, f a = ∑ a ∈ plusIdx ε, f a + ∑ a ∈ minusIdx ε, f a := by
  unfold plusIdx minusIdx
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun a => ε a = true) f]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext a
  simp
end ReciprocityTheory.ChartRestriction.DS
