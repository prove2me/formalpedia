-- Prove2me | solution 1 for PI.LocalEndW.le_one_of_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:57:11.02662+00:00
-- url     : https://prove2.me/submissions/7d350586-4ff9-46e5-8e13-4e5ae95d558e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocalEnd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_IntVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain WithZero
open PI PI.LocalEndW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocalEndW
theorem _root_.solution {N ℓ m : ℕ} (hm : 0 < m) (hmℓ : m < ℓ)
    (hN : Valued.v ((N : v.adicCompletion F)) = exp (-(m : ℤ)))
    {y z : v.adicCompletion F} (h : z ^ ℓ = 1 + N * y ^ ℓ) : Valued.v y ≤ 1 := by
  by_contra hy
  rw [not_le] at hy
  have hy0 : Valued.v y ≠ 0 := ne_of_gt (lt_trans zero_lt_one hy)
  obtain ⟨a, ha⟩ : ∃ a : ℤ, Valued.v y = exp a := ⟨_, (exp_log hy0).symm⟩
  have ha1 : 0 < a := by rw [ha, ← exp_zero, exp_lt_exp] at hy; exact hy
  have hNy : Valued.v ((N : v.adicCompletion F) * y ^ ℓ) = exp ((ℓ : ℤ) * a - m) := by
    rw [map_mul, map_pow, hN, ha, ← exp_nsmul, ← exp_add]; congr 1; simp; ring
  have hgt : Valued.v (1 : v.adicCompletion F) < Valued.v ((N : v.adicCompletion F) * y ^ ℓ) := by
    rw [hNy, map_one, ← exp_zero, exp_lt_exp]; nlinarith
  have hsum : Valued.v (1 + (N : v.adicCompletion F) * y ^ ℓ) = exp ((ℓ : ℤ) * a - m) := by
    rw [Valuation.map_add_eq_of_lt_right _ hgt, hNy]
  have hz0 : Valued.v z ≠ 0 := by
    intro h0
    rw [← h, map_pow, h0, zero_pow (by omega)] at hsum
    exact exp_ne_zero hsum.symm
  obtain ⟨c, hc⟩ : ∃ c : ℤ, Valued.v z = exp c := ⟨_, (exp_log hz0).symm⟩
  rw [← h, map_pow, hc, ← exp_nsmul, exp_inj] at hsum
  simp only [nsmul_eq_mul] at hsum
  have hd : (ℓ : ℤ) ∣ (m : ℤ) := ⟨a - c, by linarith⟩
  have := Int.le_of_dvd (by omega) hd
  omega
end PI.LocalEndW
