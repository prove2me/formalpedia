-- Prove2me | solution 1 for PI.KLW.NO.not_rp_inv_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:10:33.311871+00:00
-- url     : https://prove2.me/submissions/8230de91-abce-443d-8a05-9bb5e2b7b59f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Theorems.Thm_PI_KLW_NO_int_of_rat

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
theorem _root_.solution (hp : p.Prime) : ¬ Rp K p ((p : K)⁻¹) := by
  rintro ⟨s, hs, hsx⟩
  have h1 : (s : K) * (p : K)⁻¹ = (((s : ℚ) / p : ℚ) : K) := by push_cast; ring
  rw [h1] at hsx
  obtain ⟨m, hm⟩ := int_of_rat _ hsx
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h2 : ((s : ℤ) : ℚ) = ((p * m : ℤ) : ℚ) := by
    push_cast; rw [← hm]; field_simp
  have h3 : (p : ℤ) ∣ (s : ℤ) := ⟨m, Int.cast_injective h2⟩
  have h4 : p ∣ s := Int.natCast_dvd_natCast.1 h3
  exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hs.symm h4)
end PI.KLW.NO
