-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.descent_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:45:34.353198+00:00
-- url     : https://prove2.me/submissions/281ed5fa-3815-43c2-a60b-77e6fb8b0366

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_DescentStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open Polynomial
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {a : ℕ} {b c : ℤ} {d : ℕ}
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (hok : CmOK a b c d) {P Q r p q : ℤ} (hr : (d : ℤ) ∣ r) (hp : ¬ (d : ℤ) ∣ p)
    (hq : ¬ (d : ℤ) ∣ q) (hM : r ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q) :
    (d : ℤ) ∣ P ∧ (d : ℤ) ∣ Q := by
  obtain ⟨h4, -, h8, hdp⟩ := hok
  have hD : Prime (d : ℤ) := Nat.prime_iff_prime_int.mp hdp
  have hD0 : (d : ℤ) ≠ 0 := hD.ne_zero
  have hD2 : ¬ (d : ℤ) ∣ 2 := by
    intro h
    have h' : d ∣ 2 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  set N := P ^ 2 + P * Q * b + Q ^ 2 * (a * c) with hNdef
  have hcop : IsCoprime ((d : ℤ) ^ 2) q :=
    IsCoprime.pow_left ((Irreducible.coprime_iff_not_dvd hD.irreducible).mpr hq)
  have hdN : (d : ℤ) ^ 2 ∣ N := by
    apply hcop.dvd_of_dvd_mul_right
    rw [← hM]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hr 2) _
  have hid : 4 * N = (2 * P + b * Q) ^ 2 + d * Q ^ 2 := by
    rw [hNdef]
    linear_combination Q ^ 2 * h4
  have hX : (d : ℤ) ∣ 2 * P + b * Q := by
    apply hD.dvd_of_dvd_pow (n := 2)
    have : (2 * P + b * Q) ^ 2 = 4 * N - d * Q ^ 2 := by rw [hid]; ring
    rw [this]
    exact dvd_sub (Dvd.dvd.mul_left (dvd_trans (dvd_pow_self _ two_ne_zero) hdN) _) (dvd_mul_right _ _)
  have hQ2 : (d : ℤ) ∣ Q ^ 2 := by
    have h1 : (d : ℤ) ^ 2 ∣ d * Q ^ 2 := by
      have : (d : ℤ) * Q ^ 2 = 4 * N - (2 * P + b * Q) ^ 2 := by rw [hid]; ring
      rw [this]
      exact dvd_sub (Dvd.dvd.mul_left hdN _) (pow_dvd_pow_of_dvd hX 2)
    rw [pow_two] at h1
    exact (mul_dvd_mul_iff_left hD0).mp h1
  have hQ : (d : ℤ) ∣ Q := hD.dvd_of_dvd_pow hQ2
  have h2P : (d : ℤ) ∣ 2 * P := by
    have : 2 * P = (2 * P + b * Q) - b * Q := by ring
    rw [this]
    exact dvd_sub hX (Dvd.dvd.mul_left hQ _)
  refine ⟨?_, hQ⟩
  rcases hD.dvd_or_dvd h2P with h | h
  · exact absurd h hD2
  · exact h
end PI.UnitaryGroupMassFormula.UnimodLocStd
