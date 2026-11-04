-- Prove2me | solution 1 for ThreeSum.Histograms.tripleMass_eq_histogram_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:09.971723+00:00
-- url     : https://prove2.me/submissions/927ba500-6b13-4865-9408-f9c1016b78f9

import Definitions.Def_Submission_ThreeSum_Balancing
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Definitions.Def_Submission_ThreeSum_Histograms
import Definitions.Def_WeightedCache3SUM_Alias_6d2ffa19c0cd121d

set_option autoImplicit false
open ThreeSum ThreeSum.Histograms
open Finset
open scoped BigOperators
variable {ι τ ν G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
namespace ThreeSum.Histograms
theorem _root_.solution (A : Finset ι) (B : Finset τ) (C : Finset ν)
    (a : ι → G) (b : τ → G) (c : ν → G)
    (wa : ι → ℕ) (wb : τ → ℕ) (wc : ν → ℕ) :
    tripleMass A B C a b c wa wb wc =
      ∑ i ∈ A, wa i *
        Balancing.correlation (histogram C c wc) (histogram B b wb) (a i) := by
  unfold tripleMass
  apply sum_congr rfl
  intro i hi
  rw [correlation_histograms]
  unfold pairMass
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have heq : a i + b j = c k ↔ c k - b j = a i := by
    rw [sub_eq_iff_eq_add]
    exact eq_comm
  simp only [heq]
  split <;> simp_all [Nat.mul_assoc]
end ThreeSum.Histograms
