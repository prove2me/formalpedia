-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.keyNewton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:11:04.852335+00:00
-- url     : https://prove2.me/submissions/ac042108-c2a8-47a1-a409-0ef5ca0423df

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepNewton
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_KeyNewton
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_H_smul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_sat_rat
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_sat_sub
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_tau


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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution : KeyNewton := by
  intro a b c d ha hd lam hlam m _ _ Λ l x y T i₀ h k hk w hw
  obtain ⟨hOK, -, hθ, -, -, hl, -, -, -⟩ := h
  obtain ⟨hwsat, hwT, p, q, hq, hww⟩ := hw
  obtain ⟨τ, r, s, hτ1, hτ2, hs, hτsat⟩ := rep_tau a b c d hOK Λ hθ hl
  have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hq0 : (q : ℂ) ≠ 0 := by
    have : q ≠ 0 := by rintro rfl; exact hq (dvd_zero _)
    exact_mod_cast this
  have hs0 : (s : ℂ) ≠ 0 := by
    have : s ≠ 0 := by rintro rfl; exact hs (dvd_zero _)
    exact_mod_cast this
  set ε : ℂ := ((l ^ k * p : ℤ) : ℂ) / (q : ℂ) with hε
  have hεc : conj ε = ε := by rw [hε, map_div₀, map_intCast, map_intCast]
  have hξ : (1 - ε * τ) * conj (1 - ε * τ) = 1 - ε + ε ^ 2 * ((r : ℂ) / s) := by
    rw [map_sub, map_one, map_mul, hεc]
    linear_combination (-ε) * hτ1 + ε ^ 2 * hτ2
  refine ⟨(1 - ε * τ) • w, ?_, ?_, p ^ 2 * (r * q - s * q + l ^ k * p * r), q ^ 3 * s, ?_, ?_⟩
  · have e : (1 - ε * τ) • w = w - ε • (τ • w) := by rw [sub_smul, one_smul, smul_smul]
    rw [e, hε]
    exact rep_sat_sub l Λ hl hwsat (rep_sat_rat l Λ hl (hτsat w hwsat) _ _ hq)
  · intro j hj; simp [hwT j hj]
  · intro h
    rcases hlp.dvd_mul.mp h with h | h
    · exact hq (hlp.dvd_of_dvd_pow h)
    · exact hs h
  · rw [rep_H_smul, hξ, hww]
    rw [hε]
    push_cast
    field_simp
    ring
end PI.UnitaryGroupMassFormula.UnimodLocStd
