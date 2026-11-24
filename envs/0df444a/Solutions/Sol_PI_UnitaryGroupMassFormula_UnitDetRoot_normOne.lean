-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.normOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:39:03.458516+00:00
-- url     : https://prove2.me/submissions/aa4cc36f-7855-4cdc-9db6-d640cb96cd96

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Lemmata_GeneralBFactLeftTer_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NormLeOneOfRoot
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_norm_le_one_of_root
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_norm_iota_natCast

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution : NormOne := by
  rintro l _ ι x ⟨hx0, k, hk, h1, h2⟩
  have hI : ∀ z : ℂ, IsIntegral ℤ z → ‖ι z‖ ≤ 1 := by
    rintro z ⟨p, hp, hpz⟩
    apply norm_le_one_of_root p hp
    have h : (ι.toRingHom) (p.eval₂ (algebraMap ℤ ℂ) z) = 0 := by rw [hpz, map_zero]
    rw [Polynomial.hom_eval₂, RingHom.ext_int (ι.toRingHom.comp (algebraMap ℤ ℂ)) (Int.castRingHom _)] at h
    exact h
  have e1 := hI _ h1
  have e2 := hI _ h2
  rw [map_mul, norm_mul, norm_iota_natCast l ι k hk, one_mul] at e1 e2
  have e3 : ‖ι x‖ * ‖ι x⁻¹‖ = 1 := by
    rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
  nlinarith [norm_nonneg (ι x), norm_nonneg (ι x⁻¹)]
end PI.UnitaryGroupMassFormula.UnitDetRoot
