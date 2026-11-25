-- Prove2me | solution 1 for PI.KLW.NO.inv_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:03:08.667089+00:00
-- url     : https://prove2.me/submissions/d75611e6-7571-491c-ba83-baab4c6d36d2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Theorems.Thm_PI_KLW_NO_natCast_mem_O
import Theorems.Thm_PI_KLW_NO_intCast_mem_O
import Theorems.Thm_PI_KLW_NO_fixed_int
import Theorems.Thm_PI_KLW_NO_coprime_ne_zero
import Theorems.Thm_PI_KLW_NO_rp_div_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.NO
variable {K : Type} [Field K] [NumberField K] {p : ℕ}
namespace PI.KLW.NO
theorem _root_.solution (c : K →+* K) (hK : Module.finrank ℚ K = 2) (hne : ∃ z, c z ≠ z) (hp : p.Prime)
    {x : K} (hx : Rp K p x) (hfix : c x = x) (hnp : ¬ Rp K p (x / p)) : x ≠ 0 ∧ Rp K p x⁻¹ := by
  obtain ⟨s, hs, hsx⟩ := hx
  have hs0 : (s : K) ≠ 0 := by exact_mod_cast coprime_ne_zero hp hs
  have hfix' : c ((s : K) * x) = (s : K) * x := by rw [map_mul, map_natCast, hfix]
  obtain ⟨m, hm⟩ := fixed_int c hK hne hfix' hsx
  have hdvd : ¬ (p : ℤ) ∣ m := by
    rintro ⟨m', rfl⟩
    apply hnp
    refine ⟨s, hs, ?_⟩
    have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
    have : (s : K) * (x / p) = (m' : K) := by
      rw [mul_div_assoc', hm]; push_cast; field_simp
    rw [this]; exact intCast_mem_O m'
  have hm0 : m ≠ 0 := by rintro rfl; exact hdvd (dvd_zero _)
  have hmK : (m : K) ≠ 0 := by exact_mod_cast hm0
  have hx0 : x ≠ 0 := by
    rintro rfl; apply hmK; rw [← hm]; simp
  refine ⟨hx0, ?_⟩
  have : x⁻¹ = (s : K) / m := by rw [← hm]; field_simp
  rw [this]
  exact rp_div_int (natCast_mem_O s) hdvd hp
end PI.KLW.NO
