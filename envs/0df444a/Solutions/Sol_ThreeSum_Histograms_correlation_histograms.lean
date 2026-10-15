-- Prove2me | solution 1 for ThreeSum.Histograms.correlation_histograms
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:43:46.997316+00:00
-- url     : https://prove2.me/submissions/4c6f1ab1-23b0-4b1d-9463-18a1f9460081

import Definitions.Def_ThreeSum1962Source_Bundle01
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Exact histogram and correlation counts

All weights are natural multiplicities.  In particular, raw A incidences and
repeated selected-map occurrences need not be deduplicated to use these
identities. The common offset is chosen from the actual key histograms.
-/

namespace ThreeSum.Histograms

open Finset
open scoped BigOperators

variable {ι τ ν G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
















theorem correlation_histograms_sourceProof (I : Finset ι) (J : Finset τ)
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

end

universe u_1 u_2 u_4

theorem solution : ∀ {ι : Type u_1} {τ : Type u_2} {G : Type u_4} [inst : AddCommGroup.{u_4} G] [inst_1 : Fintype.{u_4} G]
  [inst_2 : DecidableEq.{u_4 + 1} G] (I : Finset.{u_1} ι) (J : Finset.{u_2} τ) (left : ι → G) (right : τ → G)
  (weightL : ι → Nat) (weightR : τ → Nat) (d : G),
  @Eq.{1} Nat
    (@ThreeSum.Balancing.correlation.{u_4} G inst inst_1
      (@ThreeSum.Histograms.histogram.{u_2, u_4} τ G inst_2 J right weightR)
      (@ThreeSum.Histograms.histogram.{u_1, u_4} ι G inst_2 I left weightL) d)
    (@ThreeSum.Histograms.pairMass.{u_1, u_2, u_4} ι τ G inst inst_2 I J left right weightL weightR d) := by
  exact @ThreeSum.Histograms.correlation_histograms_sourceProof

#print axioms solution
