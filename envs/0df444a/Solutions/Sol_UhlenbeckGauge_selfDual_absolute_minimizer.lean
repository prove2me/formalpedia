-- Prove2me | solution 1 for UhlenbeckGauge.selfDual_absolute_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-10T21:44:56.879426+00:00
-- url     : https://prove2.me/submissions/ca0bbcd4-1e8e-4a62-9eb4-bcb95e49e018

import Definitions.Def_uhlenbeck_gauge_box_defs
import Theorems.Thm_UhlenbeckGauge_yangMills_ge_boundaryChernSimons
import Theorems.Thm_UhlenbeckGauge_yangMills_eq_boundaryChernSimons_iff
import Theorems.Thm_UhlenbeckGauge_boundaryChernSimons_eq_of_eq_on_boundary

open UhlenbeckGauge MeasureTheory
set_option autoImplicit false

/-- Proposition 3.1.1 (box version). On a non-degenerate box, the (anti-)self-dual `A` attains
the energy bound with equality, `Ym(A) = ∓ Re ∫_{∂Ω} CS(A)`; the Chern–Simons boundary term of
`A` equals that of `B` because the two connections agree on `∂Ω`; and `B` satisfies the energy
bound `Ym(B) ≥ ∓ Re ∫_{∂Ω} CS(B)`. On a degenerate box both energies vanish. -/
theorem solution {n : ℕ} (a b : R4) (A B : Connection n)
    (hA : IsSUConnection A) (hB : IsSUConnection B)
    (hbdry : ∀ x, OnBoxBoundary a b x → A x = B x)
    (hdual : (∀ x ∈ Set.Icc a b, IsSelfDual (curvature A x)) ∨
      (∀ x ∈ Set.Icc a b, IsAntiSelfDual (curvature A x))) :
    yangMills a b A ≤ yangMills a b B := by
  by_cases hlt : ∀ μ, a μ < b μ
  · have hab : a ≤ b := fun μ => (hlt μ).le
    -- the boundary term is determined by the boundary data
    have hCS : boundaryChernSimons a b A = boundaryChernSimons a b B :=
      boundaryChernSimons_eq_of_eq_on_boundary a b hab A B hA hB hbdry
    -- energy bound for `B`, both signs
    obtain ⟨hB1, hB2⟩ := yangMills_ge_boundaryChernSimons a b hab B hB
    -- equality case for `A`
    obtain ⟨hA1, hA2⟩ := yangMills_eq_boundaryChernSimons_iff a b hlt A hA
    rcases hdual with h | h
    · rw [hA1.mpr h, hCS]
      exact hB1
    · rw [hA2.mpr h, hCS]
      exact hB2
  · -- degenerate box: `[a, b]` is a null set, so both energies are `0`
    push Not at hlt
    obtain ⟨μ, hμ⟩ := hlt
    have hvol : volume (Set.Icc a b) = 0 := by
      rw [Real.volume_Icc_pi]
      exact Finset.prod_eq_zero (Finset.mem_univ μ) (by simp [hμ])
    have h0 : ∀ C : Connection n, yangMills a b C = 0 := fun C => by
      unfold yangMills
      rw [Measure.restrict_eq_zero.mpr hvol, integral_zero_measure]
    rw [h0 A, h0 B]
