-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casimirK_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:45:16.206269+00:00
-- url     : https://prove2.me/submissions/4cff9a8d-9312-4438-986d-2cec4be2021f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mul_mul_sub_mul_mul_eq_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ite_mul_sub_mul_ite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ite_sub_add_sub_eq

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
theorem _root_.solution (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E)
    (c d : Fin n) (hcd : ε c = ε d) :
    casimirK ε E * E c d = E c d * casimirK ε E := by
  unfold IsGlRep at hE
  rw [← sub_eq_zero]
  unfold casimirK
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ite_mul_sub_mul_ite, mul_mul_sub_mul_mul_eq_add, hE]
  simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero]
  simp only [ite_sub_add_sub_eq, ← ite_and, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [and_comm (b := _ = c), and_comm (b := d = _), Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and, Finset.mem_univ, if_true]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [hcd]
  abel
end ReciprocityTheory.ChartRestriction.DS
