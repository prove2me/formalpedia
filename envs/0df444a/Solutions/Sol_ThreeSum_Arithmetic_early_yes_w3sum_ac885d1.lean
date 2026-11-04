-- Prove2me | solution 1 for ThreeSum.Arithmetic.early_yes_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:20:07.973028+00:00
-- url     : https://prove2.me/submissions/98b639d3-ed1e-4f05-9683-1b7b89a48493

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_Arithmetic_sum_fiberWeight
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero

set_option autoImplicit false
open ThreeSum ThreeSum.Arithmetic
open Finset
open scoped BigOperators
namespace ThreeSum.Arithmetic
theorem _root_.solution {ι τ : Type*} [Fintype τ] [DecidableEq τ]
    (I : Finset ι) (owner : ι → τ) (weight : ι → ℕ)
    (good : τ → Prop) [DecidablePred good] (Rmax H : ℕ)
    (hcap : ∀ t : τ, ¬ good t → fiberWeight I owner weight t ≤ Rmax)
    (hcount : (Finset.univ.filter (fun t : τ => ¬ good t)).card ≤ H)
    (hlarge : Rmax * H < ∑ i ∈ I, weight i) :
    ∃ i ∈ I, 0 < weight i ∧ good (owner i) := by
  classical
  by_contra hnone
  have hzero : ∀ i ∈ I, good (owner i) → weight i = 0 := by
    intro i hi hg
    by_contra hw
    exact hnone ⟨i, hi, Nat.pos_of_ne_zero hw, hg⟩
  have hbound : ∀ t : τ, fiberWeight I owner weight t ≤
      if good t then 0 else Rmax := by
    intro t
    by_cases ht : good t
    · simp only [if_pos ht]
      have hz : fiberWeight I owner weight t = 0 := by
        unfold fiberWeight
        apply Finset.sum_eq_zero
        intro i hi
        by_cases he : owner i = t
        · simp [he, hzero i hi (he.symm ▸ ht)]
        · simp [he]
      omega
    · simpa [ht] using hcap t ht
  have hsum : (∑ t : τ, if good t then (0 : ℕ) else Rmax) =
      (Finset.univ.filter (fun t : τ => ¬ good t)).card * Rmax := by
    calc
      (∑ t : τ, if good t then (0 : ℕ) else Rmax) =
          ∑ t ∈ Finset.univ.filter (fun t : τ => ¬ good t), Rmax := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro t ht
        by_cases hg : good t <;> simp [hg]
      _ = _ := by simp
  have htotal : (∑ i ∈ I, weight i) ≤ Rmax * H := by
    calc
      (∑ i ∈ I, weight i) = ∑ t : τ, fiberWeight I owner weight t :=
        (sum_fiberWeight I owner weight).symm
      _ ≤ ∑ t : τ, if good t then 0 else Rmax :=
        Finset.sum_le_sum (fun t ht => hbound t)
      _ = (Finset.univ.filter (fun t : τ => ¬ good t)).card * Rmax := hsum
      _ ≤ H * Rmax := Nat.mul_le_mul_right Rmax hcount
      _ = Rmax * H := Nat.mul_comm _ _
  omega
end ThreeSum.Arithmetic
