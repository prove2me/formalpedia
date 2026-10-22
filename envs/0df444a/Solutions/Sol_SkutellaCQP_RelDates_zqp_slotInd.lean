-- Prove2me | solution 1 for SkutellaCQP.RelDates.zqp_slotInd
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:46:07.918659+00:00
-- url     : https://prove2.me/submissions/a4af0e6f-bc99-4e6c-950e-1e456ff1197b

import Mathlib
import Definitions.Def_SkutellaCQP_RelDates_Setting

set_option autoImplicit false
open Finset SkutellaCQP.RelDates

theorem solution {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (hr : ∀ i j, 0 ≤ r i j)
    (τ : Fin n → Fin m × Fin n) :
    ZQPrel p w r (slotInd τ) = ∑ j, w j * Cslot p w r τ j := by
  unfold ZQPrel
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 1
  have key : ∀ X : Fin m → Fin n → ℝ,
      ∑ i, ∑ k, slotInd τ i k j * X i k = X (τ j).1 (τ j).2 := by
    intro X
    rw [Finset.sum_eq_single (τ j).1]
    · rw [Finset.sum_eq_single (τ j).2]
      · simp [slotInd]
      · intro k _ hk
        have : τ j ≠ ((τ j).1, k) := fun h => hk (by rw [h])
        simp [slotInd, this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro i _ hi
      refine Finset.sum_eq_zero (fun k _ => ?_)
      have : τ j ≠ (i, k) := fun h => hi (by rw [h])
      simp [slotInd, this]
    · intro h; exact absurd (Finset.mem_univ _) h
  have := key (fun i k => sStart p r (slotInd τ) i k + (1 + slotInd τ i k j) / 2 * p i j +
      ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w i j' j), slotInd τ i k j' * p i j')
  rw [this]
  unfold Cslot
  have h1 : slotInd τ (τ j).1 (τ j).2 j = 1 := by simp [slotInd]
  rw [h1]
  have h2 : ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w (τ j).1 j' j),
        slotInd τ (τ j).1 (τ j).2 j' * p (τ j).1 j' =
      ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w (τ j).1 j' j ∧ τ j' = τ j),
        p (τ j).1 j' := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    by_cases h : SkutellaCQP.NoRel.prec p w (τ j).1 j' j <;> by_cases h' : τ j' = τ j <;>
      simp [slotInd, h, h', Prod.mk.eta]
  rw [h2]; ring
