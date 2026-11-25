-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.Phi_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:08:55.022849+00:00
-- url     : https://prove2.me/submissions/119a8d08-2c89-4442-bd4e-21926eb88fbd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryApproxFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_sgl_mul
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
theorem _root_.solution (x y : E ⊗[F] Fv F v) : Phi v (x * y) = Phi v x * Phi v y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul e' a' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, Phi_tmul, Phi_tmul, Phi_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, sgl_mul]
    | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
  | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
end PI.UnitaryGroupMassFormula.UJClassMass
