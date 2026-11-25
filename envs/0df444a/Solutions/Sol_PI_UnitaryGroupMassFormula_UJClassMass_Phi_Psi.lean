-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.Phi_Psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:13:01.769425+00:00
-- url     : https://prove2.me/submissions/1afa54ae-722f-45a3-97b6-4911e3be30eb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryApproxFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_sgl_one_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_Psi_tmul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_Phi_tmul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct RestrictedProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (r : Af F ⊗[F] E) : Phi v (Psi v r) = (sgl v 1 ⊗ₜ[F] (1 : E)) * r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Psi_tmul, Phi_tmul, Algebra.TensorProduct.tmul_mul_tmul, sgl_one_mul, one_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]
end PI.UnitaryGroupMassFormula.UJClassMass
