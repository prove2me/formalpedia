-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.mul_mul_sub_mul_mul_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:01.783376+00:00
-- url     : https://prove2.me/submissions/2da3c9d5-693b-4ce2-80b3-17e674daf606

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd

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
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {R : Type*} [Ring R] (X Y Z : R) :
    X * Y * Z - Z * (X * Y) = (X * Z - Z * X) * Y + X * (Y * Z - Z * Y) := by
  noncomm_ring
end ReciprocityTheory.ChartRestriction.DS
