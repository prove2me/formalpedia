-- Prove2me | solution 1 for PelagicFF.pelagic_mass_ge
-- status  : ACCEPTED   (prove)
-- author  : @dargilboa
-- created : 2026-11-15T08:59:56.249203+00:00
-- url     : https://prove2.me/submissions/6f3d6e21-266c-413e-a2ba-1b3c8424ee3c

import Mathlib
import Definitions.Def_PelagicFF_PFF
import Theorems.Thm_OAI_Cotype_parseval

open OAI.Cotype
open Classical

namespace PelagicFF

/-- If every `y ∈ S` has lower mass `∑_{a z ≤ a y} w z < c`, then `S` itself has mass `≤ c`:
the element of `S` with the largest `a` dominates all of `S`. -/
private theorem mass_low_le {α : Type} [Fintype α] (a w : α → ℝ) (hw : ∀ z, 0 ≤ w z)
    (c : ℝ) (hc : 0 ≤ c) (S : Finset α)
    (hS : ∀ y ∈ S, ∑ z ∈ Finset.univ.filter (fun z => a z ≤ a y), w z < c) :
    ∑ y ∈ S, w y ≤ c := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simpa using hc
  · obtain ⟨y₀, hy₀, hmax⟩ := S.exists_max_image a hne
    refine le_trans ?_ (hS y₀ hy₀).le
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun z _ _ => hw z)
    intro y hy
    simpa using hmax y hy

/-- If every `y ∈ S` has upper mass `∑_{a y ≤ a z} w z < c`, then `S` itself has mass `≤ c`:
the element of `S` with the smallest `a` is dominated by all of `S`. -/
private theorem mass_high_le {α : Type} [Fintype α] (a w : α → ℝ) (hw : ∀ z, 0 ≤ w z)
    (c : ℝ) (hc : 0 ≤ c) (S : Finset α)
    (hS : ∀ y ∈ S, ∑ z ∈ Finset.univ.filter (fun z => a y ≤ a z), w z < c) :
    ∑ y ∈ S, w y ≤ c := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simpa using hc
  · obtain ⟨y₀, hy₀, hmin⟩ := S.exists_min_image a hne
    refine le_trans ?_ (hS y₀ hy₀).le
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun z _ _ => hw z)
    intro y hy
    simpa using hmin y hy

/-- Parseval for a `±1`-valued function: the squared Fourier coefficients sum to `1`. -/
private theorem fourier_sq_sum_eq_one (n : ℕ) (H : (Fin n → Bool) → Bool) :
    ∑ y, OAI.Cotype.fourier (fun x => sign (H x)) y ^ 2 = 1 := by
  rw [OAI.Cotype.parseval]
  have h1 : ∀ ε : Fin n → Bool, sign (H ε) ^ 2 = 1 := by
    intro ε
    cases H ε <;> simp [sign]
  have hc : (Fintype.card (Fin n → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := Fin n → Bool))
  simp only [average, h1, smul_eq_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ hc

/-- For a nonnegative weight, the mass of a union is at most the sum of the masses. -/
private theorem sum_union_le' {α : Type} [DecidableEq α] (w : α → ℝ) (hw : ∀ z, 0 ≤ w z)
    (s t : Finset α) : ∑ y ∈ s ∪ t, w y ≤ ∑ y ∈ s, w y + ∑ y ∈ t, w y := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := w)
  have h0 : 0 ≤ ∑ y ∈ s ∩ t, w y := Finset.sum_nonneg (fun z _ => hw z)
  linarith

end PelagicFF

open PelagicFF in
theorem solution (n : ℕ) (H : (Fin n → Bool) → Bool) :
    (3 : ℝ) / 4 ≤ ∑ y ∈ Finset.univ.filter (fun y => IsPelagic (fun x => sign (H x)) y),
      OAI.Cotype.fourier (fun x => sign (H x)) y ^ 2 := by
  set F : (Fin n → Bool) → ℝ := OAI.Cotype.fourier (fun x => sign (H x)) with hF
  set a : (Fin n → Bool) → ℝ := fun y => |F y| with ha
  set w : (Fin n → Bool) → ℝ := fun y => F y ^ 2 with hw
  have hw0 : ∀ z, 0 ≤ w z := fun z => sq_nonneg _
  -- the two bad sets
  set L : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun y => ∑ z ∈ Finset.univ.filter (fun z => a z ≤ a y), w z < 1 / 8)
    with hL
  set U : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun y => ∑ z ∈ Finset.univ.filter (fun z => a y ≤ a z), w z < 1 / 8)
    with hU
  set P : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun y => IsPelagic (fun x => sign (H x)) y) with hP
  have hLm : ∑ y ∈ L, w y ≤ 1 / 8 :=
    mass_low_le a w hw0 (1 / 8) (by norm_num) L (fun y hy => (Finset.mem_filter.mp hy).2)
  have hUm : ∑ y ∈ U, w y ≤ 1 / 8 :=
    mass_high_le a w hw0 (1 / 8) (by norm_num) U (fun y hy => (Finset.mem_filter.mp hy).2)
  -- every frequency is Pelagic or in one of the bad sets
  have hcover : (Finset.univ : Finset (Fin n → Bool)) ⊆ P ∪ (L ∪ U) := by
    intro y _
    by_cases hy : IsPelagic (fun x => sign (H x)) y
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩)
    · refine Finset.mem_union_right _ ?_
      unfold IsPelagic at hy
      rw [not_and_or] at hy
      rcases hy with h | h
      · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ y, ?_⟩)
        have h' := not_le.mp h
        convert h' using 2
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ y, ?_⟩)
        have h' := not_le.mp h
        convert h' using 2
  have htotal : ∑ y, w y = 1 := fourier_sq_sum_eq_one n H
  have h1 : ∑ y, w y ≤ ∑ y ∈ P ∪ (L ∪ U), w y :=
    Finset.sum_le_sum_of_subset_of_nonneg hcover (fun z _ _ => hw0 z)
  have h2 : ∑ y ∈ P ∪ (L ∪ U), w y ≤ ∑ y ∈ P, w y + ∑ y ∈ L ∪ U, w y :=
    sum_union_le' w hw0 P (L ∪ U)
  have h3 : ∑ y ∈ L ∪ U, w y ≤ ∑ y ∈ L, w y + ∑ y ∈ U, w y :=
    sum_union_le' w hw0 L U
  linarith
