-- Prove2me | solution 1 for PI.KLW.NO.unit_of_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:09:28.105176+00:00
-- url     : https://prove2.me/submissions/6c7c9b58-a08f-458d-a741-ec421f0f795a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Theorems.Thm_PI_KLW_NO_rp_mul
import Theorems.Thm_PI_KLW_NO_rp_c
import Theorems.Thm_PI_KLW_NO_inv_of_fixed

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
theorem _root_.solution (c : K →+* K) (hc : ∀ x, c (c x) = x) (hK : Module.finrank ℚ K = 2)
    (hne : ∃ z, c z ≠ z) (hp : p.Prime) {z : K} (hz : Rp K p z) (hn : ¬ Rp K p (z * c z / p)) :
    z ≠ 0 ∧ Rp K p z⁻¹ := by
  have hfix : c (z * c z) = z * c z := by rw [map_mul, hc, mul_comm]
  obtain ⟨h0, hinv⟩ := inv_of_fixed c hK hne hp (rp_mul hz (rp_c c hz)) hfix hn
  have hz0 : z ≠ 0 := by rintro rfl; simp at h0
  have hcz0 : c z ≠ 0 := by rintro h; apply h0; rw [h, mul_zero]
  refine ⟨hz0, ?_⟩
  have : z⁻¹ = c z * (z * c z)⁻¹ := by field_simp
  rw [this]; exact rp_mul (rp_c c hz) hinv
end PI.KLW.NO
