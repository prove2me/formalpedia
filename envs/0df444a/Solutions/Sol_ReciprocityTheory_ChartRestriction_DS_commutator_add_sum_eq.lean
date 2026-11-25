-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.commutator_add_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:21:15.874922+00:00
-- url     : https://prove2.me/submissions/6f25b7f1-73db-43e1-96c1-14c0c549e9f8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep

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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {R : Type*} [Ring R] {k : ℕ} (m m' : R) (s s' : Fin k → R)
    (h1 : ∀ j, m * s' j = s' j * m) (h2 : ∀ i, s i * m' = m' * s i)
    (h3 : ∀ i j, i ≠ j → s i * s' j = s' j * s i) :
    (m + ∑ i, s i) * (m' + ∑ j, s' j) - (m' + ∑ j, s' j) * (m + ∑ i, s i) =
      (m * m' - m' * m) + ∑ i, (s i * s' i - s' i * s i) := by
  simp only [add_mul, mul_add, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have e1 : ∑ j, m * s' j = ∑ j, s' j * m := Finset.sum_congr rfl fun j _ => h1 j
  have e2 : ∑ i, s i * m' = ∑ i, m' * s i := Finset.sum_congr rfl fun i _ => h2 i
  have e3 : ∑ x, ∑ i, s i * s' x - ∑ x, ∑ i, s' i * s x = ∑ i, (s i * s' i - s' i * s i) := by
    rw [Finset.sum_comm (f := fun x i => s' i * s x), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_eq_single x (fun i _ hix => sub_eq_zero.2 (h3 i x hix)) (by simp)
  rw [e1, e2, ← e3]
  abel
end ReciprocityTheory.ChartRestriction.DS
