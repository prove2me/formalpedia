-- Prove2me | solution 1 for QuantumMaxCutEnergy.energy_le_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:50:28.087194+00:00
-- url     : https://prove2.me/submissions/4d70b686-2a5c-4ddd-86fa-f698c71b24f1

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEnergy_prodState

/-!
# The energy of any state is bounded by a multiple of its norm

`optimum G` is the supremum of `energy G.weights ψ` over normalised `ψ`, so to prove that some
candidate value is below the optimum we need the energy set to be bounded above. This file proves
the quantitative bound

  `energy w ψ ≤ 2 (Σ_e w e) * ‖ψ‖²`,

so normalised states satisfy `energy w ψ ≤ 2 Σ_e w e`, and hence
`energy w ψ ≤ optimum ⟨n, w⟩` for every normalised `ψ`.

The only non-mechanical ingredient is the reindexing `Σ x, f (x ∘ swap) = Σ x, f x`, which is
`Equiv.sum_comp` along precomposition by the swap.
-/

open Complex
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- Precomposition by an equivalence of the index type. -/
def precompEquiv {ι : Type*} {α : Type*} (e : ι ≃ ι) : (ι → α) ≃ (ι → α) where
  toFun x := x ∘ e
  invFun x := x ∘ e.symm
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp

/-- The swap of two coordinates reindexes a sum over basis vectors. -/
theorem sum_comp_swap_proof {n : ℕ} (a b : Fin n) (f : (Basis n) → ℝ) :
    (∑ x : Basis n, f (fun i => x (Equiv.swap a b i)))
      = ∑ x : Basis n, f x := by
  have h := Equiv.sum_comp (precompEquiv (α := Bool) (Equiv.swap a b)) f
  exact h

/-- `|a − b|² ≤ 2|a|² + 2|b|²` for complex numbers. -/
theorem normSq_sub_le_proof (a b : ℂ) :
    Complex.normSq (a - b) ≤ 2 * Complex.normSq a + 2 * Complex.normSq b := by
  have h1 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
  have h2 : Complex.normSq (a - b) = ‖a - b‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have h3 : Complex.normSq a = ‖a‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have h4 : Complex.normSq b = ‖b‖ ^ 2 := Complex.normSq_eq_norm_sq _
  nlinarith [norm_nonneg (a - b), norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖)]

/-- **Energy bound.** `energy w ψ ≤ 2 (Σ_e w e) ‖ψ‖²`. -/
theorem energy_le_two_mul_proof (n : ℕ) (w : Weights n) (ψ : Wave n) :
    energy w ψ ≤ 2 * (∑ e, (w e : ℝ)) * squaredNorm ψ := by
  have hterm : ∀ e : Edge n,
      (w e : ℝ) / 2 * ∑ x, Complex.normSq (ψ x - ψ (x ∘ Equiv.swap e.val.1 e.val.2))
        ≤ (w e : ℝ) / 2 * (4 * squaredNorm ψ) := by
    intro e
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑ x : Fin n → Bool, Complex.normSq (ψ x - ψ (x ∘ Equiv.swap e.val.1 e.val.2))
        ≤ ∑ x, (2 * Complex.normSq (ψ x) + 2 * Complex.normSq (ψ (x ∘ Equiv.swap e.val.1 e.val.2))) :=
          Finset.sum_le_sum fun x _ => normSq_sub_le_proof (ψ x) (ψ (x ∘ Equiv.swap e.val.1 e.val.2))
      _ = 2 * (∑ x, Complex.normSq (ψ x)) + 2 * (∑ x, Complex.normSq (ψ (x ∘ Equiv.swap e.val.1 e.val.2))) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = 2 * (∑ x, Complex.normSq (ψ x)) + 2 * (∑ x, Complex.normSq (ψ x)) := by
          have hswap : (∑ x, Complex.normSq (ψ (x ∘ Equiv.swap e.val.1 e.val.2)))
              = ∑ x, Complex.normSq (ψ x) :=
            sum_comp_swap_proof e.val.1 e.val.2 (fun y => Complex.normSq (ψ y))
          rw [hswap]
      _ = 4 * squaredNorm ψ := by
          unfold squaredNorm
          ring
  calc energy w ψ
      = ∑ e, (w e : ℝ) / 2 * ∑ x, Complex.normSq (ψ x - ψ (x ∘ Equiv.swap e.val.1 e.val.2)) := rfl
    _ ≤ ∑ e, (w e : ℝ) / 2 * (4 * squaredNorm ψ) := Finset.sum_le_sum fun e _ => hterm e
    _ = 2 * (∑ e, (w e : ℝ)) * squaredNorm ψ := by
        have hfac : ∀ e : Edge n, (w e : ℝ) / 2 * (4 * squaredNorm ψ)
            = ((w e : ℝ) * 2) * squaredNorm ψ := fun e => by ring
        simp only [hfac, ← Finset.sum_mul]
        ring


end QuantumMaxCutEnergy

open QuantumMaxCutEnergy in
theorem solution (n : ℕ) (w : QuantumMaxCutEnergy.Weights n) (ψ : QuantumMaxCutEnergy.Wave n) :
    QuantumMaxCutEnergy.energy w ψ
      ≤ 2 * (∑ e, (w e : ℝ)) * QuantumMaxCutEnergy.squaredNorm ψ :=
  QuantumMaxCutEnergy.energy_le_two_mul_proof n w ψ
