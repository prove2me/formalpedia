-- Prove2me | solution 1 for ThreeSum.Histograms.correlation_histograms_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:45.268291+00:00
-- url     : https://prove2.me/submissions/5547474f-8732-41b2-b1ee-ca5bee30de71

import Definitions.Def_Submission_ThreeSum_Balancing
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Definitions.Def_Submission_ThreeSum_Histograms

set_option autoImplicit false
open ThreeSum ThreeSum.Histograms
open Finset
open scoped BigOperators
variable {ι τ ν G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
namespace ThreeSum.Histograms
theorem _root_.solution (I : Finset ι) (J : Finset τ)
    (left : ι → G) (right : τ → G) (weightL : ι → ℕ) (weightR : τ → ℕ) (d : G) :
    Balancing.correlation (histogram J right weightR) (histogram I left weightL) d =
      pairMass I J left right weightL weightR d := by
  unfold Balancing.correlation histogram pairMass
  simp_rw [sum_mul, mul_sum]
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [sum_comm]
  have hinner (i : ι) :
      (∑ k : G, (if right j = k then weightR j else 0) *
        (if left i = k - d then weightL i else 0)) =
      if right j - left i = d then weightL i * weightR j else 0 := by
    simp only [ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]
    by_cases h : right j - left i = d
    · have h' : left i = right j - d := by exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm)
      simp [h, h', Nat.mul_comm]
    · have h' : left i ≠ right j - d := by
        intro h'
        apply h
        rw [h']
        abel
      simp [h, h']
  simp_rw [hinner]
end ThreeSum.Histograms
