-- Prove2me | solution 1 for ThreeSum.TernaryCoverMoments.moment_bound_of_classes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:08:34.160477+00:00
-- url     : https://prove2.me/submissions/5614468c-4fe8-48d4-ba6f-626e382e98e3

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverMoments
import Theorems.Thm_ThreeSum_TernaryCoverMoments_sum_incidenceCount_pow
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverMoments
open Finset
open scoped BigOperators
variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]
namespace ThreeSum.TernaryCoverMoments
theorem _root_.solution {C : Type*} [Fintype C] [DecidableEq C]
    (events : E → Finset Ω) (k p : ℕ) (hp : 0 < p)
    (classify : (Fin k → E) → C) (rank : C → ℕ)
    (hcount : ∀ c : C, (univ.filter fun es => classify es = c).card ≤ p ^ rank c)
    (hhash : ∀ es : Fin k → E,
      p ^ rank (classify es) * (jointEvent events es).card ≤ Fintype.card Ω) :
    (∑ w, HashFamily.incidenceCount events w ^ k) ≤ Fintype.card C * Fintype.card Ω := by
  classical
  rw [sum_incidenceCount_pow]
  have hclass (c : C) :
      (∑ es ∈ (univ.filter fun es => classify es = c), (jointEvent events es).card) ≤
        Fintype.card Ω := by
    apply Nat.le_of_mul_le_mul_left (c := p ^ rank c) ?_ (Nat.pow_pos hp)
    rw [mul_sum]
    calc
      _ ≤ ∑ _es ∈ (univ.filter fun es => classify es = c), Fintype.card Ω := by
        apply sum_le_sum
        intro es hes
        have hc := (mem_filter.mp hes).2
        simpa [hc] using hhash es
      _ = (univ.filter fun es : Fin k → E => classify es = c).card * Fintype.card Ω := by simp
      _ ≤ p ^ rank c * Fintype.card Ω := Nat.mul_le_mul_right _ (hcount c)
  have hsplit : (∑ es : Fin k → E, (jointEvent events es).card) =
      ∑ c : C, ∑ es ∈ (univ.filter fun es => classify es = c), (jointEvent events es).card := by
    simp_rw [sum_filter]
    rw [sum_comm]
    simp
  rw [hsplit]
  calc
    _ ≤ ∑ _c : C, Fintype.card Ω := sum_le_sum (fun c _ => hclass c)
    _ = Fintype.card C * Fintype.card Ω := by simp
end ThreeSum.TernaryCoverMoments
