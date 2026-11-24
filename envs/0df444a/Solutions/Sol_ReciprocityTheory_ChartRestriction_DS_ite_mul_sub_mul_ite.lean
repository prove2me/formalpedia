-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.ite_mul_sub_mul_ite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:57.899604+00:00
-- url     : https://prove2.me/submissions/a0bc2716-c089-4764-afe4-b6582e6dffd9

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
theorem _root_.solution {R : Type*} [Ring R] (p : Prop) [Decidable p] (X Z : R) :
    (if p then X else 0) * Z - Z * (if p then X else 0) = if p then X * Z - Z * X else 0 := by
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.DS
