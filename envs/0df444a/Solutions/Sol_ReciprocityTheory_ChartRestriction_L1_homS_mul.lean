-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.homS_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:42.125523+00:00
-- url     : https://prove2.me/submissions/5a7d5b1c-636a-4409-9528-b9aaf5dfd2e5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProjA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_homS_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_homS_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable {K : Type} [Field K] (U : PowerSeries K)
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (m n : ℕ) (P Q : K[X]) (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) :
    homS U (m + n) (P * Q) = homS U m P * homS U n Q := by
  have eP : P = ∑ i ∈ Finset.range (m + 1), monomial i (P.coeff i) :=
    P.as_sum_range' (m + 1) (Nat.lt_succ_of_le hP)
  have eQ : Q = ∑ j ∈ Finset.range (n + 1), monomial j (Q.coeff j) :=
    Q.as_sum_range' (n + 1) (Nat.lt_succ_of_le hQ)
  have e : P * Q = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      monomial (i + j) (P.coeff i * Q.coeff j) := by
    conv_lhs => rw [eP, eQ]
    rw [Finset.sum_mul_sum]
    simp only [monomial_mul_monomial]
  rw [e, homS_sum]
  simp only [homS_sum]
  unfold homS
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have := homS_monomial U (m + n) (i + j) (by omega) (P.coeff i * Q.coeff j)
  unfold homS at this
  rw [this]
  have h2 : 2 * (m + n - (i + j)) = 2 * (m - i) + 2 * (n - j) := by omega
  rw [h2, pow_add, pow_add, map_mul]
  ring
end ReciprocityTheory.ChartRestriction.L1
