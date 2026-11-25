-- Prove2me | solution 1 for PI.AlgValsFin.W.classSame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:09:51.709789+00:00
-- url     : https://prove2.me/submissions/29df3e12-c12c-4591-8032-34494076a77b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_OrdFEqOfClassOf
import Theorems.Thm_PI_AlgValsFin_W_ordAt_eU
import Theorems.Thm_PI_AlgValsFin_W_ordF_eq_of_classOf
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_ordAt_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
namespace PI.AlgValsFin.W
theorem _root_.solution : ClassSame L := by
  classical
  refine ⟨ClassGroup (𝓞 L), inferInstance, fun v => classOf L (eU v), fun v w hvw => ?_⟩
  have h1 : classOf L (eU v * (eU w)⁻¹) = 1 := by
    have hvw' : classOf L (eU v) = classOf L (eU w) := hvw
    rw [map_mul, map_inv, hvw', mul_inv_cancel]
  obtain ⟨k, hk⟩ := ordF_eq_of_classOf _ h1
  refine ⟨k, fun u => ?_⟩
  rw [hk, ordAt_mul, ordAt_inv, ordAt_eU, ordAt_eU]
  ring
end PI.AlgValsFin.W
