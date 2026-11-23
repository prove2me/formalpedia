-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casimir_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:15.743873+00:00
-- url     : https://prove2.me/submissions/e08bf03b-5f8f-417b-be28-76fa4b7c1406

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mul_mul_sub_mul_mul_eq_add

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
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (c d : Fin n) :
    casimir E * E c d = E c d * casimir E := by
  unfold IsGlRep at hE
  rw [← sub_eq_zero]
  unfold casimir
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, mul_mul_sub_mul_mul_eq_add, hE]
  simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  abel
end ReciprocityTheory.ChartRestriction.DS
