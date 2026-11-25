-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.norm_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:30.918609+00:00
-- url     : https://prove2.me/submissions/686e2f04-0724-4699-a62b-1beeae03a146

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_DescentStep
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_descent_step
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_theta_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_apply



set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open Polynomial
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {a : ℕ} {b c : ℤ} {d : ℕ}
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (hok : CmOK a b c d) {γ : ℂ} (hγ : IsK b d γ) {p q : ℤ} (hp : ¬ (d : ℤ) ∣ p)
    (hq : ¬ (d : ℤ) ∣ q) (hN : γ * conj γ = (p : ℂ) / q) : ∃ s : ℤ, (d : ℤ) ∣ s ^ 2 * q - p := by
  obtain ⟨h4, ha, h8, hdp⟩ := hok
  have hD : Prime (d : ℤ) := Nat.prime_iff_prime_int.mp hdp
  have hD0 : (d : ℤ) ≠ 0 := hD.ne_zero
  have hD2 : ¬ (d : ℤ) ∣ 2 := by
    intro h
    have h' : d ∣ 2 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hq (dvd_zero _)
  have hθ : cmTheta b d * (b - cmTheta b d) = (a : ℂ) * c := by
    have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp
    have h4' : (4 * a * c : ℂ) = b ^ 2 + d := by exact_mod_cast h4
    unfold cmTheta
    linear_combination (-(((Real.sqrt d : ℝ) : ℂ) ^ 2) / 4) * Complex.I_sq + (1 / 4 : ℂ) * hs +
      (-1 / 4 : ℂ) * h4'

  have rel : ∀ P Q r : ℤ, (r : ℂ) * γ = P + Q * cmTheta b d →
      r ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q := by
    intro P Q r hr
    have h1 : (r : ℂ) * γ * conj ((r : ℂ) * γ) = r ^ 2 * ((p : ℂ) / q) := by
      rw [map_mul, map_intCast, ← hN]
      ring
    have h2 : (r : ℂ) * γ * conj ((r : ℂ) * γ) = P ^ 2 + P * Q * b + Q ^ 2 * (a * c) := by
      rw [hr, map_add, map_mul, map_intCast, map_intCast, theta_conj]
      linear_combination (Q : ℂ) ^ 2 * hθ
    have hq0' : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
    have hC : (r : ℂ) ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q := by
      rw [← h2, h1]
      field_simp
    exact_mod_cast hC

  have main : ∀ n : ℕ, ∀ P Q r : ℤ, r.natAbs = n → r ≠ 0 →
      r ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q → ∃ s : ℤ, (d : ℤ) ∣ s ^ 2 * q - p := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P Q r hn hr0 hM
      by_cases hdr : (d : ℤ) ∣ r
      · obtain ⟨hP, hQ⟩ := descent_step ⟨h4, ha, h8, hdp⟩ hdr hp hq hM
        obtain ⟨P', rfl⟩ := hP
        obtain ⟨Q', rfl⟩ := hQ
        obtain ⟨r', rfl⟩ := hdr
        have hr' : r' ≠ 0 := by
          rintro rfl
          simp at hr0
        have hM' : r' ^ 2 * p = (P' ^ 2 + P' * Q' * b + Q' ^ 2 * (a * c)) * q := by
          have hd2 : ((d : ℤ) ^ 2) ≠ 0 := pow_ne_zero 2 hD0
          apply mul_left_cancel₀ hd2
          linear_combination hM
        refine ih r'.natAbs ?_ P' Q' r' rfl hr' hM'
        rw [← hn, Int.natAbs_mul]
        have h1 : 1 < (d : ℤ).natAbs := by
          have := hdp.two_le
          simp only [Int.natAbs_natCast]
          omega
        have h2 : 0 < r'.natAbs := Int.natAbs_pos.mpr hr'
        nlinarith
      · have := Fact.mk hdp
        have hkey : (2 * r) ^ 2 * p = (2 * P + b * Q) ^ 2 * q + d * (Q ^ 2 * q) := by
          linear_combination 4 * hM + q * Q ^ 2 * h4
        have h2r : ((2 * r : ℤ) : ZMod d) ≠ 0 := by
          rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
          intro h
          rcases hD.dvd_or_dvd h with h | h
          · exact hD2 h
          · exact hdr h
        refine ⟨((((2 * P + b * Q : ℤ) : ZMod d) * ((2 * r : ℤ) : ZMod d)⁻¹).val : ℤ), ?_⟩
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        have hk := congrArg (Int.cast : ℤ → ZMod d) hkey
        push_cast at hk h2r ⊢
        rw [ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, add_zero] at *
        have hinv : (2 * (r : ZMod d))⁻¹ ^ 2 * (2 * (r : ZMod d)) ^ 2 = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ h2r, one_pow]
        linear_combination (-((2 * (r : ZMod d))⁻¹ ^ 2)) * hk + (p : ZMod d) * hinv
  obtain ⟨P, Q, r, hr0, hr⟩ := hγ
  exact main r.natAbs P Q r rfl hr0 (rel P Q r hr)
end PI.UnitaryGroupMassFormula.UnimodLocStd
