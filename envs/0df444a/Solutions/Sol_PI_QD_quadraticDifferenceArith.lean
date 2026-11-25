-- Prove2me | solution 1 for PI.QD.quadraticDifferenceArith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:06:24.091866+00:00
-- url     : https://prove2.me/submissions/e3f60195-c81e-43a1-8934-3ef8f954e58c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuadDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDifference_QuadDiffOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDifference_QuadraticDifferenceForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.QD
open NumberField Polynomial
namespace PI.QD
theorem _root_.solution : Arith := by
  unfold Arith
  intro d x y hsq hd4 ⟨u, hu⟩ ⟨N, hN⟩
  obtain ⟨M, hM⟩ : ∃ M : ℤ, (d : ℚ) * (2 * y) ^ 2 = M := ⟨4 * N - u ^ 2, by
    push_cast
    linear_combination 4 * hN - (2 * x + (u : ℚ)) * hu⟩
  obtain ⟨w, hw⟩ : ∃ w : ℚ, w = 2 * y := ⟨_, rfl⟩
  rw [← hw] at hM
  have h2 : w * w.den = w.num := Rat.mul_den_eq_num w
  have h3 : ((d * w.num ^ 2 : ℤ) : ℚ) = ((M * (w.den : ℤ) ^ 2 : ℤ) : ℚ) := by
    push_cast
    rw [← h2]
    linear_combination (w.den : ℚ) ^ 2 * hM
  have key : (d : ℤ) * w.num ^ 2 = M * (w.den : ℤ) ^ 2 := by exact_mod_cast h3
  have hcop : IsCoprime ((w.den : ℤ) ^ 2) (w.num ^ 2) :=
    (Int.isCoprime_iff_gcd_eq_one.mpr (show Int.gcd w.num (w.den : ℤ) = 1 from w.reduced)).symm.pow
  have hdvd : (w.den : ℤ) ^ 2 ∣ (d : ℤ) := by
    apply hcop.dvd_of_dvd_mul_right
    exact ⟨M, by rw [key]; ring⟩
  have hdvd' : w.den * w.den ∣ d := by
    rw [← pow_two]
    exact_mod_cast hdvd
  have hden : w.den = 1 := Nat.isUnit_iff.mp (hsq _ hdvd')
  rw [hden, Nat.cast_one, mul_one] at h2
  obtain ⟨v, hv⟩ : ∃ v : ℤ, v = w.num := ⟨_, rfl⟩
  rw [← hv] at h2 key
  rw [hden] at key
  have hE : u ^ 2 + (d : ℤ) * v ^ 2 = 4 * N := by
    have h4 : ((u ^ 2 + (d : ℤ) * v ^ 2 : ℤ) : ℚ) = ((4 * N : ℤ) : ℚ) := by
      push_cast
      rw [← h2, hw]
      linear_combination 4 * hN - (2 * x + (u : ℚ)) * hu
    exact_mod_cast h4
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (d : ℤ) = 4 * t + 3 := ⟨((d / 4 : ℕ) : ℤ), by omega⟩
  rw [ht] at hE
  have hpar : ∃ a : ℤ, u - v = 2 * a := by
    rcases Int.even_or_odd' u with ⟨k, hk | hk⟩ <;> rcases Int.even_or_odd' v with ⟨m, hm | hm⟩ <;>
      subst hk <;> subst hm
    · exact ⟨k - m, by ring⟩
    · exfalso
      ring_nf at hE
      omega
    · exfalso
      ring_nf at hE
      omega
    · exact ⟨k - m, by ring⟩
  obtain ⟨a, ha⟩ := hpar
  refine ⟨a, v, ?_, ?_⟩
  · have ha' : ((u - v : ℤ) : ℚ) = ((2 * a : ℤ) : ℚ) := by rw [ha]
    push_cast at ha'
    linear_combination hu / 2 + ha' / 2
  · rw [← h2, hw]
    ring
end PI.QD
