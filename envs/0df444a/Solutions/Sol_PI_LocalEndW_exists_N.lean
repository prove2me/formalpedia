-- Prove2me | solution 1 for PI.LocalEndW.exists_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:57:13.695503+00:00
-- url     : https://prove2.me/submissions/6c03b665-c633-4de1-bfcb-c17fcef629f6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocalEnd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_IntVal
import Theorems.Thm_PI_LocalEndW_val_natCast

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
theorem _root_.solution : ∃ N : ℕ, 0 < N ∧ ∃ m : ℕ, 0 < m ∧
    Valued.v ((N : v.adicCompletion F)) = exp (-(m : ℤ)) ∧
    ∀ ℓ : ℕ, ℓ.Prime → N < ℓ → Valued.v ((ℓ : v.adicCompletion F)) = 1 := by
  set N := Ideal.absNorm v.asIdeal with hN
  have hNmem : ((N : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have hNpos : 0 < N := by
    rw [Nat.pos_iff_ne_zero, hN, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hN0 : ((N : ℕ) : 𝓞 F) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hlt : v.intValuation (N : 𝓞 F) < 1 := (v.intValuation_lt_one_iff_mem _).2 hNmem
  have hne : v.intValuation (N : 𝓞 F) ≠ 0 := v.intValuation_ne_zero _ hN0
  obtain ⟨k, hk⟩ : ∃ k : ℤ, v.intValuation (N : 𝓞 F) = exp k := ⟨_, (exp_log hne).symm⟩
  have hk0 : k < 0 := by rw [hk, ← exp_zero, exp_lt_exp] at hlt; exact hlt
  refine ⟨N, hNpos, (-k).toNat, by omega, ?_, ?_⟩
  · rw [val_natCast, hk]; congr 1; omega
  · intro ℓ hℓ hNℓ
    rw [val_natCast, HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl, Ideal.mem_primeCompl_iff]
    intro hmem
    have hcop : Nat.Coprime ℓ N :=
      (Nat.Prime.coprime_iff_not_dvd hℓ).2 (Nat.not_dvd_of_pos_of_lt hNpos hNℓ)
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have h1 : (a : 𝓞 F) * (ℓ : 𝓞 F) + (b : 𝓞 F) * (N : 𝓞 F) = 1 := by
      have := congrArg (Int.cast : ℤ → 𝓞 F) hab
      push_cast at this
      exact this
    have : (1 : 𝓞 F) ∈ v.asIdeal := by
      rw [← h1]
      exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hmem) (v.asIdeal.mul_mem_left _ hNmem)
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
end PI.LocalEndW
