-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.carKinv_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:35.421277+00:00
-- url     : https://prove2.me/submissions/ad7794a4-c3e1-4854-b8aa-5e7a28047106

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
theorem _root_.solution {R : Type*} [Ring R] (P Q A S : R) (hQA : Q * A = A * Q)
    (hPS : P * S = S * P) :
    P * Q * (A + S) - (A + S) * (P * Q) = (P * A - A * P) * Q - P * (S * Q - Q * S) := by
  calc P * Q * (A + S) - (A + S) * (P * Q)
      = (P * A - A * P) * Q - P * (S * Q - Q * S) + P * (Q * A - A * Q) + (P * S - S * P) * Q := by
        noncomm_ring
    _ = (P * A - A * P) * Q - P * (S * Q - Q * S) := by
        rw [hQA, hPS, sub_self, sub_self, mul_zero, zero_mul, add_zero, add_zero]
end ReciprocityTheory.ChartRestriction.DS
