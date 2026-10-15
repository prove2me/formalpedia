-- Prove2me | solution 1 for ThreeSum.Histograms.tripleMass_eq_histogram
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:11:44.727374+00:00
-- url     : https://prove2.me/submissions/1419f20d-1dd5-4658-8612-71b85f7a9066

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
import Theorems.Thm_ThreeSum_Histograms_correlation_histograms


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






































































/-- One B/C correlation is shared by every A value in the band. -/
theorem tripleMass_eq_histogram_sourceProof (A : Finset ι) (B : Finset τ) (C : Finset ν)
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

end

universe u_1 u_2 u_3 u_4

theorem solution : ∀ {ι : Type u_1} {τ : Type u_2} {ν : Type u_3} {G : Type u_4} [inst : AddCommGroup.{u_4} G] [inst_1 : Fintype.{u_4} G]
  [inst_2 : DecidableEq.{u_4 + 1} G] (A : Finset.{u_1} ι) (B : Finset.{u_2} τ) (C : Finset.{u_3} ν) (a : ι → G)
  (b : τ → G) (c : ν → G) (wa : ι → Nat) (wb : τ → Nat) (wc : ν → Nat),
  @Eq.{1} Nat (@ThreeSum.Histograms.tripleMass.{u_1, u_2, u_3, u_4} ι τ ν G inst inst_2 A B C a b c wa wb wc)
    (∑ i ∈ A,
      @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (wa i)
        (@ThreeSum.Balancing.correlation.{u_4} G inst inst_1
          (@ThreeSum.Histograms.histogram.{u_3, u_4} ν G inst_2 C c wc)
          (@ThreeSum.Histograms.histogram.{u_2, u_4} τ G inst_2 B b wb) (a i))) := by
  exact @ThreeSum.Histograms.tripleMass_eq_histogram_sourceProof

#print axioms solution
