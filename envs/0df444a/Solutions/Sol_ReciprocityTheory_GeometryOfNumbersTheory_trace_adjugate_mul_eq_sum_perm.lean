-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.trace_adjugate_mul_eq_sum_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:46.022324+00:00
-- url     : https://prove2.me/submissions/2527b0a8-8d65-4b45-8003-7592acde6a36

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_LogDetSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Matrix MeasureTheory
open scoped ComplexOrder
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℂ) :
    (A.adjugate * B).trace = ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℂ) *
      ∑ i, (∏ j ∈ Finset.univ.erase i, A (σ j) j) • B (σ i) i := by
  have hcol : ∀ i, (A.adjugate * B) i i = ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℂ) *
      ((∏ j ∈ Finset.univ.erase i, A (σ j) j) • B (σ i) i) := by
    intro i
    have h1 : (A.adjugate * B) i i = (A.updateCol i (fun k => B k i)).det := by
      rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [h1, Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), smul_eq_mul, mul_comm]
    congr 1
    all_goals first
      | (refine Finset.prod_congr rfl fun j hj => ?_
         simp [Matrix.updateCol_apply, Finset.ne_of_mem_erase hj])
      | simp [Matrix.updateCol_apply]
  simp only [Matrix.trace, Matrix.diag, hcol]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
end ReciprocityTheory.GeometryOfNumbersTheory
