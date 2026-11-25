-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.qequiv_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:46:08.04612+00:00
-- url     : https://prove2.me/submissions/7b3cde56-0f1d-4492-af06-c497bf078e4f

import Definitions.Def_Formalism_PeriodIntegrals_UnimodLocStd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_QequivApply
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_qequiv_apply

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V)
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (hsym : ∀ x y, H y x = conj (H x y)) (z : V) {c : ℂ} (hc0 : c ≠ 0)
    (hc : c + conj c = H z z) : IsIsom H H (qequiv H z hc0 hc : V →ₗ[ℂ] V) := by
  intro x y
  have hc1 : conj c ≠ 0 := by simpa using hc0
  simp only [LinearEquiv.coe_coe]
  rw [qequiv_apply, qequiv_apply]
  simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, map_mul, map_inv₀,
    RingHom.id_apply, hsym y z, ← hc]
  field_simp
  ring
end PI.UnitaryGroupMassFormula.UnimodLocStd
