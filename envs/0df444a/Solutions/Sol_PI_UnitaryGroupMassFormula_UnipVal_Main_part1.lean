-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnipVal.Main.part1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:56:28.667909+00:00
-- url     : https://prove2.me/submissions/d567b85a-1c35-4ffb-b460-8a45f9d492bc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnipVal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentValuation_VwIntEqZero
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnipVal_Main_vw_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnipVal_Main_vw_pow
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnipVal_Main_vw_int_eq_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnipVal_Main_plc_prime
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnipVal_Main_natCast_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnipVal PI.UnitaryGroupMassFormula.UnipVal.Main
open PI.UnipVal
variable {K : Type} [Field K] [NumberField K]
namespace PI.UnitaryGroupMassFormula.UnipVal.Main
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : n ≠ 0) :
    vw w ((n : ℕ) : K) = ramw w * (padicValNat (plc w) n : ℤ) := by
  have hp := plc_prime w
  haveI : Fact (plc w).Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := pow_padicValNat_dvd (p := plc w) (n := n)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hn (by simpa using hm)
  have hpm : ¬ plc w ∣ m := by
    rintro ⟨c, rfl⟩
    exact pow_succ_padicValNat_not_dvd hn ⟨c, hm.trans (by ring)⟩
  have hmw : ((m : 𝓞 K)) ∉ w.asIdeal := by
    rw [natCast_mem_iff]
    exact hpm
  have hm0' : ((m : 𝓞 K)) ≠ 0 := by
    intro h
    apply hmw
    rw [h]
    exact w.asIdeal.zero_mem
  have hval := vw_int_eq_zero w (m : 𝓞 K) hm0' hmw
  rw [map_natCast] at hval
  have hpK : ((plc w : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hmK : ((m : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  conv_lhs => rw [hm]
  rw [Nat.cast_mul, Nat.cast_pow, vw_mul w (pow_ne_zero _ hpK) hmK, vw_pow, hval, ramw]
  ring
end PI.UnitaryGroupMassFormula.UnipVal.Main
