-- Prove2me | solution 1 for ValuationSubring.not_mem_and_inv_not_mem_of_dominates_of_residuallyAlgebraic_of_forall_isUnit_polynomialEval2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/43f50a40-cc63-5277-b053-e31ce8ea6752

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_not_mem_and_inv_not_mem_of_dominates_of_residuallyAlgebraic_of_forall_isUnit_polynomialEval2

set_option autoImplicit false

open IsLocalRing

theorem solution
    {A₀ : Type} [CommRing A₀] {F : Type} [Field F] (j₀ : A₀ →+* F)
    (O : ValuationSubring F) (S : Subring F)
    (hSO : S ≤ O.toSubring)

    (hdom : ∀ s ∈ S, s⁻¹ ∉ S → s ∈ O.nonunits)

    (halg : ∀ s ∈ S, ∃ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) ∧
      (Polynomial.eval₂ j₀ s p = 0 ∨ (Polynomial.eval₂ j₀ s p ∈ S ∧ (Polynomial.eval₂ j₀ s p)⁻¹ ∉ S)))
    (g : F)
    (hgeo : ∀ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) →
      ∃ hO : Polynomial.eval₂ j₀ g p ∈ O, IsUnit (⟨_, hO⟩ : ↥O)) :
    g ∉ S ∧ g⁻¹ ∉ S := by
  classical

  have hgeo' : ∀ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) → O.valuation (Polynomial.eval₂ j₀ g p) = 1 := by
    intro p hp
    obtain ⟨hO, hu⟩ := hgeo p hp
    exact (ValuationSubring.valuation_eq_one_iff O ⟨_, hO⟩).mp hu

  have hX : O.valuation g = 1 := by
    have := hgeo' Polynomial.X ⟨1, by simp⟩
    simpa [Polynomial.eval₂_X] using this
  have hg0 : g ≠ 0 := fun h => by rw [h, map_zero] at hX; exact zero_ne_one hX

  haveI hA₀ : Nontrivial A₀ := ⟨⟨0, 1, fun h => by
    have h' := congrArg j₀ h
    rw [map_zero, map_one] at h'
    exact zero_ne_one h'⟩⟩
  refine ⟨fun hgS => ?_, fun hgS => ?_⟩
  · obtain ⟨p, hp, h⟩ := halg g hgS
    have h1 := hgeo' p hp
    rcases h with h0 | ⟨hpS, hpinv⟩
    · rw [h0, map_zero] at h1
      exact zero_ne_one h1
    · have h2 := hdom _ hpS hpinv
      rw [ValuationSubring.mem_nonunits_iff] at h2
      exact absurd h1 (ne_of_lt h2)
  · obtain ⟨p, hp, h⟩ := halg g⁻¹ hgS

    have hrev : ∃ i, IsUnit (p.reverse.coeff i) := by
      obtain ⟨i, hi⟩ := hp
      have hi0 : p.coeff i ≠ 0 := hi.ne_zero
      have hile : i ≤ p.natDegree := Polynomial.le_natDegree_of_ne_zero hi0
      refine ⟨p.natDegree - i, ?_⟩
      rw [Polynomial.coeff_reverse, Polynomial.revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hile]
      exact hi
    have h1 := hgeo' p.reverse hrev

    have hid : Polynomial.eval₂ j₀ g p.reverse * g⁻¹ ^ p.natDegree = Polynomial.eval₂ j₀ g⁻¹ p := by
      haveI : Invertible g⁻¹ := invertibleOfNonzero (inv_ne_zero hg0)
      have := Polynomial.eval₂_reverse_mul_pow j₀ g⁻¹ p
      rwa [invOf_eq_inv, inv_inv] at this
    have hval : O.valuation (Polynomial.eval₂ j₀ g⁻¹ p) = 1 := by
      rw [← hid, map_mul, map_pow, map_inv₀, h1, hX]
      simp
    rcases h with h0 | ⟨hpS, hpinv⟩
    · rw [h0, map_zero] at hval
      exact zero_ne_one hval
    · have h2 := hdom _ hpS hpinv
      rw [ValuationSubring.mem_nonunits_iff] at h2
      exact absurd hval (ne_of_lt h2)

end S_ValuationSubring_not_mem_and_inv_not_mem_of_dominates_of_residuallyAlgebraic_of_forall_isUnit_polynomialEval2
end P2MW
export P2MW.S_ValuationSubring_not_mem_and_inv_not_mem_of_dominates_of_residuallyAlgebraic_of_forall_isUnit_polynomialEval2 (solution)
