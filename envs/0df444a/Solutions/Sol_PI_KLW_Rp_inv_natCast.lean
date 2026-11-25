-- Prove2me | solution 1 for PI.KLW.Rp_inv_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:48:01.408118+00:00
-- url     : https://prove2.me/submissions/03ccdab5-36f8-4723-9148-564ac0b99901

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Theorems.Thm_PI_KLW_mem_range_iff

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
open PI PI.KLW
variable {K : Type} [Field K] [NumberField K]
namespace PI.KLW
theorem _root_.solution {p : ℕ} {s : ℕ} (hs : Nat.Coprime s p) : Rp K p ((s : K)⁻¹) := by
  refine ⟨s, hs, ?_⟩
  rw [mem_range_iff]
  by_cases h : (s : K) = 0
  · rw [h, zero_mul]; exact isIntegral_zero
  · rw [mul_inv_cancel₀ h]; exact isIntegral_one
end PI.KLW
