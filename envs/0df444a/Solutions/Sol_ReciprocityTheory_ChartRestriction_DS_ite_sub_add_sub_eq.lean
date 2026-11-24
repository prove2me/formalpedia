-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.ite_sub_add_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:58.379255+00:00
-- url     : https://prove2.me/submissions/367c967c-0823-4ba9-8ff8-0a71c36dd6b4

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
theorem _root_.solution {R : Type*} [AddCommGroup R] (p : Prop) [Decidable p] (A B C D : R) :
    (if p then (A - B) + (C - D) else 0) =
      ((if p then A else 0) - (if p then B else 0)) + ((if p then C else 0) - (if p then D else 0)) := by
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.DS
