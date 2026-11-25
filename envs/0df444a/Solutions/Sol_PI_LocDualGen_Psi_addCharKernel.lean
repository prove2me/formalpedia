-- Prove2me | solution 1 for PI.LocDualGen.Psi.addCharKernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:57:12.554687+00:00
-- url     : https://prove2.me/submissions/e7d7a26b-8c36-4983-9886-8ad2b02f68d4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_AddCharKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.LocDualGen PI.LocDualGen.Psi
open PI.LocDualGen.W
namespace PI.LocDualGen.Psi
theorem _root_.solution : PsiKer := by
  rintro l _ t a ⟨n, hn⟩ ht
  have hI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hexp : Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) = 1 ↔ a.den = 1 := by
    rw [Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨m, hm⟩
      rw [mul_comm (m : ℂ)] at hm
      have h1 : (a : ℂ) = (m : ℂ) := mul_left_cancel₀ hI hm
      have ha : a = m := by exact_mod_cast h1
      rw [ha]
      exact Rat.den_intCast m
    · intro h1
      refine ⟨a.num, ?_⟩
      have ha : (a : ℂ) = (a.num : ℂ) := by
        have h := (Rat.den_eq_one_iff a).mp h1
        exact_mod_cast h.symm
      rw [ha]
      ring
  have hna : ‖t‖ ≤ 1 ↔ ‖(a : ℚ_[l])‖ ≤ 1 := by
    constructor
    · intro h
      have e : (a : ℚ_[l]) = t + ((a : ℚ_[l]) - t) := by ring
      rw [e]
      refine le_trans (Padic.nonarchimedean _ _) (max_le h ?_)
      rw [norm_sub_rev]
      exact ht
    · intro h
      have e : t = (t - (a : ℚ_[l])) + (a : ℚ_[l]) := by ring
      rw [e]
      exact le_trans (Padic.nonarchimedean _ _) (max_le ht h)
  have hrat : ‖(a : ℚ_[l])‖ ≤ 1 ↔ a.den = 1 := by
    constructor
    · intro h
      by_contra hd
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hn
        exact hd hn
      have hlp : l.Prime := Fact.out
      have hnum : ¬ (l : ℤ) ∣ a.num := by
        intro hdvd
        have h1 : l ∣ a.num.natAbs := Int.natCast_dvd.mp hdvd
        have h2 : l ∣ a.den := by
          rw [hn]
          exact dvd_pow_self l hn0
        have h3 := Nat.dvd_gcd h1 h2
        rw [a.reduced.gcd_eq_one] at h3
        exact hlp.one_lt.ne' (Nat.dvd_one.mp h3)
      have hnum1 : ‖(a.num : ℚ_[l])‖ = 1 :=
        le_antisymm (Padic.norm_int_le_one _)
          (not_lt.mp fun h' => hnum (Padic.norm_intCast_lt_one_iff.mp h'))
      have hden : ‖(a.den : ℚ_[l])‖ = ((l : ℝ)⁻¹) ^ n := by
        rw [hn, Nat.cast_pow, norm_pow, Padic.norm_p]
      have ha : (a : ℚ_[l]) = (a.num : ℚ_[l]) / (a.den : ℚ_[l]) := by
        rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
      rw [ha, norm_div, hnum1, hden] at h
      have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
      have hgt : (1 : ℝ) < 1 / ((l : ℝ)⁻¹) ^ n := by
        rw [inv_pow, one_div, inv_inv]
        exact one_lt_pow₀ hl1 hn0
      linarith
    · intro h1
      have ha : (a : ℚ_[l]) = (a.num : ℚ_[l]) := by
        have h := (Rat.den_eq_one_iff a).mp h1
        norm_cast
        exact h.symm
      rw [ha]
      exact Padic.norm_int_le_one _
  rw [hexp, hna, hrat]
end PI.LocDualGen.Psi
