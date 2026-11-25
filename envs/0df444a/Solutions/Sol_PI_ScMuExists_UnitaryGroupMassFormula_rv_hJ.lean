-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.rv_hJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:29:15.30502+00:00
-- url     : https://prove2.me/submissions/4b6bb1fc-dd62-4049-8e91-a3c8000852ec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_phi_star
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_gram_real
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_hJ_mulVec_gen
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
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution (v : NumberField.InfinitePlace I.F) (x y : Fin I.n → I.E) :
    hJ (I.ε v) (rv I v x) (rv I v y) = I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  simp only [rv]
  rw [hJ_mulVec_gen, gram_real I v]
  simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, Pi.star_apply,
    Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply, phi_star I v]
  ring
end PI.ScMuExists.UnitaryGroupMassFormula
