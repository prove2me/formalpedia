-- Prove2me | solution 1 for UpperTheory.formal_group_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:07:41.55497+00:00
-- url     : https://prove2.me/submissions/8b0ad534-9466-4b18-bb94-2f58e58c1f96

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FormalGroupCoeffMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem coeff_mul_mem_of_lt {R : Type} [CommRing R] (S : Subring R) (n : ℕ)
    (f g : PowerSeries R) (hf : ∀ k < n, PowerSeries.coeff k f ∈ S)
    (hg : ∀ k < n, PowerSeries.coeff k g ∈ S) :
    ∀ k < n, PowerSeries.coeff k (f * g) ∈ S := by
  intro k hk
  rw [PowerSeries.coeff_mul]
  refine S.sum_mem fun p hp => ?_
  have hp' : p.1 + p.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  exact S.mul_mem (hf _ (by omega)) (hg _ (by omega))
private theorem coeff_mul_mem_step {R : Type} [CommRing R] (S : Subring R) (n : ℕ)
    (f g : PowerSeries R) (hf0 : PowerSeries.constantCoeff f = 0)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hf : ∀ k < n, PowerSeries.coeff k f ∈ S)
    (hg : ∀ k < n, PowerSeries.coeff k g ∈ S) :
    PowerSeries.coeff n (f * g) ∈ S := by
  rw [PowerSeries.coeff_mul]
  refine S.sum_mem fun p hp => ?_
  have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases h1 : p.1 = 0
  · rw [h1, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0, zero_mul]
    exact S.zero_mem
  by_cases h2 : p.2 = 0
  · rw [h2, PowerSeries.coeff_zero_eq_constantCoeff_apply, hg0, mul_zero]
    exact S.zero_mem
  exact S.mul_mem (hf _ (by omega)) (hg _ (by omega))
end

set_option autoImplicit false

namespace UpperTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (S : Subring R) (a₁ a₂ a₃ a₄ a₆ : R) (w : PowerSeries R), a₁ ∈ S → a₂ ∈ S → a₃ ∈ S → a₄ ∈ S → a₆ ∈ S → PowerSeries.constantCoeff w = 0 → w = PowerSeries.X ^ 3 + PowerSeries.C a₁ * PowerSeries.X * w + PowerSeries.C a₂ * PowerSeries.X ^ 2 * w + PowerSeries.C a₃ * w ^ 2 + PowerSeries.C a₄ * PowerSeries.X * w ^ 2 + PowerSeries.C a₆ * w ^ 3 → ∀ n, PowerSeries.coeff n w ∈ S := by
  intro R _ S a₁ a₂ a₃ a₄ a₆ w h₁ h₂ h₃ h₄ h₆ h0 hw n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hX : ∀ k < n, PowerSeries.coeff k (PowerSeries.X : PowerSeries R) ∈ S := by
      intro k _
      rw [PowerSeries.coeff_X]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    have hX0 : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0 :=
      PowerSeries.constantCoeff_X
    have hX3 : PowerSeries.coeff n ((PowerSeries.X : PowerSeries R) ^ 3) ∈ S := by
      rw [PowerSeries.coeff_X_pow]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    have hXw0 : PowerSeries.constantCoeff (PowerSeries.X * w) = 0 := by
      rw [map_mul, h0, mul_zero]
    have hww0 : PowerSeries.constantCoeff (w * w) = 0 := by
      rw [map_mul, h0, mul_zero]
    have hXw := coeff_mul_mem_of_lt S n _ _ hX ih
    have hww := coeff_mul_mem_of_lt S n _ _ ih ih
    have e : w = PowerSeries.X ^ 3 + PowerSeries.C a₁ * (PowerSeries.X * w)
        + PowerSeries.C a₂ * (PowerSeries.X * (PowerSeries.X * w))
        + PowerSeries.C a₃ * (w * w) + PowerSeries.C a₄ * (PowerSeries.X * (w * w))
        + PowerSeries.C a₆ * (w * (w * w)) := by
      refine hw.trans ?_
      ring
    have e' := congrArg (PowerSeries.coeff n) e
    rw [e']
    simp only [map_add, PowerSeries.coeff_C_mul]
    exact S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem hX3
      (S.mul_mem h₁ (coeff_mul_mem_step S n _ _ hX0 h0 hX ih)))
      (S.mul_mem h₂ (coeff_mul_mem_step S n _ _ hX0 hXw0 hX hXw)))
      (S.mul_mem h₃ (coeff_mul_mem_step S n _ _ h0 h0 ih ih)))
      (S.mul_mem h₄ (coeff_mul_mem_step S n _ _ hX0 hww0 hX hww)))
      (S.mul_mem h₆ (coeff_mul_mem_step S n _ _ h0 hww0 ih hww))
end UpperTheory
