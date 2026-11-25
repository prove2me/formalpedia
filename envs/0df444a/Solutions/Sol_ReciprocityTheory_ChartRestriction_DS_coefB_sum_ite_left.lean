-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefB_sum_ite_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:20:18.861429+00:00
-- url     : https://prove2.me/submissions/5d8eaebd-0a39-430f-98ed-e5b072a2608a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefAInnerEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefBTensSubKStable

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
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (a : Fin n) (x : D) (v : Fin n → D) :
    ∑ c, inner ℂ (if c = a then x else 0) (v c) = inner ℂ x (v a) := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro c _ hc
    simp [hc]
  · simp
end ReciprocityTheory.ChartRestriction.DS
