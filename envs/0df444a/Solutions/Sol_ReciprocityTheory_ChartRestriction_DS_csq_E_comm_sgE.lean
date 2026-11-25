-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.csq_E_comm_sgE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:30.103691+00:00
-- url     : https://prove2.me/submissions/b93942a4-2c59-4fbd-b1d6-b7eec561d45d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqB

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
theorem _root_.solution {E cp cm : Fin n → Fin n → Module.End ℂ W} (hEC : CommutesCAR E cp cm)
    (ε : Fin n → Bool) (x y a b : Fin n) :
    E x y * sgE ε cp cm a b = sgE ε cp cm a b * E x y := by
  unfold sgE
  split_ifs
  · rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← mul_assoc, (hEC x y a z).1, mul_assoc, (hEC x y b z).2, ← mul_assoc]
  · rw [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, (hEC x y i b).1, mul_assoc, (hEC x y i a).2, ← mul_assoc]
  · rw [mul_zero, zero_mul]
end ReciprocityTheory.ChartRestriction.DS
