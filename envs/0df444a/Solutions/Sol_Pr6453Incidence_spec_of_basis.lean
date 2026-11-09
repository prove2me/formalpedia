-- Prove2me | solution 1 for Pr6453Incidence.spec_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @gustasmickus
-- created : 2026-11-08T22:50:20.55022+00:00
-- url     : https://prove2.me/submissions/5fea748c-f4e9-4a43-9453-71db8a76a605

/-
PR #6453: checking the incidence on basis pairs suffices.
-/
import Mathlib

set_option autoImplicit false

namespace Pr6453Incidence

open Finset

variable {ι κ n : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype n]

/-- **The finite verification principle for the incidence.** `enc a b` is the row vector the word
reads when its input rows are filled with the coefficient vectors `a` (of the first multiplicand) and
`b` (of the second); `M` is the word; `read` reads the CRT coordinates of the target rows; `P` is the
product in that basis. All four are linear in each slot, so if the word produces the right answer on
the basis pairs, it produces it on every pair. -/
theorem spec_of_basis
    (enc : (ι → ℚ) →ₗ[ℚ] (ι → ℚ) →ₗ[ℚ] (n → ℚ))
    (M : (n → ℚ) →ₗ[ℚ] (n → ℚ))
    (read : (n → ℚ) →ₗ[ℚ] (κ → ℚ))
    (P : (ι → ℚ) →ₗ[ℚ] (ι → ℚ) →ₗ[ℚ] (κ → ℚ))
    (hbasis : ∀ i j, read (M (enc (Pi.single i (1:ℚ)) (Pi.single j (1:ℚ)))) =
      P (Pi.single i (1:ℚ)) (Pi.single j (1:ℚ))) :
    ∀ a b : ι → ℚ, read (M (enc a b)) = P a b := by
  intro a b
  have ha : a = ∑ i, a i • (Pi.single i (1 : ℚ) : ι → ℚ) := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl, mul_one]
    · intro x _ hx
      rw [if_neg (Ne.symm hx), mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  have hb : b = ∑ j, b j • (Pi.single j (1 : ℚ) : ι → ℚ) := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl, mul_one]
    · intro x _ hx
      rw [if_neg (Ne.symm hx), mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  conv_lhs => rw [ha, hb]
  conv_rhs => rw [ha, hb]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [hbasis]

end Pr6453Incidence

/-- **Checking the incidence on basis pairs suffices.** -/
theorem solution {ι κ n : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype n]
    (enc : (ι → ℚ) →ₗ[ℚ] (ι → ℚ) →ₗ[ℚ] (n → ℚ))
    (M : (n → ℚ) →ₗ[ℚ] (n → ℚ))
    (read : (n → ℚ) →ₗ[ℚ] (κ → ℚ))
    (P : (ι → ℚ) →ₗ[ℚ] (ι → ℚ) →ₗ[ℚ] (κ → ℚ))
    (hbasis : ∀ i j, read (M (enc (Pi.single i 1) (Pi.single j 1))) =
      P (Pi.single i 1) (Pi.single j 1)) :
    ∀ a b : ι → ℚ, read (M (enc a b)) = P a b :=
  Pr6453Incidence.spec_of_basis enc M read P hbasis
