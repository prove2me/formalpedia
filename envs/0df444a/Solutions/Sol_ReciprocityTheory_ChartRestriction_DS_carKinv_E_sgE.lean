-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.carKinv_E_sgE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:35.285979+00:00
-- url     : https://prove2.me/submissions/a41a89fa-2fbc-4593-b441-c1670dd414b3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARKinv

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
    (ε : Fin n → Bool) (a b c d : Fin n) : E c d * sgE ε cp cm a b = sgE ε cp cm a b * E c d := by
  have key : ∀ x y u v, E c d * (cp x y * cm u v) = cp x y * cm u v * E c d := by
    intro x y u v
    rw [← mul_assoc, (hEC c d x y).1, mul_assoc, (hEC c d u v).2, ← mul_assoc]
  unfold sgE
  split_ifs
  · rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => key _ _ _ _
  · rw [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun x _ => key _ _ _ _)
  · simp
end ReciprocityTheory.ChartRestriction.DS
