-- Prove2me | solution 1 for PI.ScRefExists.GlueB.hG_nsmul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:35:39.572333+00:00
-- url     : https://prove2.me/submissions/f0aaa96b-a868-4d41-9bc2-7aadcd702b7e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HypsNonvacuous
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HGNsmulRight
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GlueB
open PI.ScRefExists PI.ScRefExists.GlueA PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst) (g : ℕ)
namespace PI.ScRefExists.GlueB
theorem _root_.solution (m : ℕ) (x y : Fin I.n → I.E) :
    Formalism.UG.hform (starRingEnd I.E) I.J (m • x) y = (m : I.E) * Formalism.UG.hform (starRingEnd I.E) I.J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end PI.ScRefExists.GlueB
