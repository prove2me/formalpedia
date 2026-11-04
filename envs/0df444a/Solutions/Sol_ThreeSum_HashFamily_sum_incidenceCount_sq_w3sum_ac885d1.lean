-- Prove2me | solution 1 for ThreeSum.HashFamily.sum_incidenceCount_sq_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:38.076244+00:00
-- url     : https://prove2.me/submissions/7574aa6b-5ce4-4888-890a-2cacdde2ddce

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_HashFamily
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_HashFamily_incidenceCount_eq_sum
attribute [local simp] ThreeSum.HashFamily.hashMap_apply

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]
namespace ThreeSum.HashFamily
theorem _root_.solution (events : E → Finset Ω) :
    (∑ w, incidenceCount events w ^ 2) =
      ∑ e, ∑ f, (events e ∩ events f).card := by
  calc
    (∑ w, incidenceCount events w ^ 2) =
        ∑ w, ∑ e, ∑ f,
          if w ∈ events e ∧ w ∈ events f then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [incidenceCount_eq_sum, pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      by_cases he : w ∈ events e <;> by_cases hf : w ∈ events f <;> simp [he, hf]
    _ = ∑ e, ∑ f, ∑ w,
          if w ∈ events e ∧ w ∈ events f then (1 : ℕ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      exact Finset.sum_comm
    _ = ∑ e, ∑ f, (events e ∩ events f).card := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro f hf
      simp [← Finset.mem_inter]
end ThreeSum.HashFamily
