-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LSC.LatIs.latSet_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:17.51335+00:00
-- url     : https://prove2.me/submissions/862b25f7-b631-48c2-bb10-571bced58c8e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatSizeContOfSteps
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Theorems.Thm_PI_UnitaryGroupMassFormula_LSC_LatIs_lamAf_eq
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
open NumberField
open scoped TensorProduct
open PI.LatSizeCont
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LSC
open PI.UnitaryGroupMassFormula.LSC.LatIs
namespace PI.UnitaryGroupMassFormula.LSC.LatIs
theorem _root_.solution (I : Formalism.MainNotions.S.AutInst) (x : I.GA) :
    Size.latSet I x = (Formalism.UG.CS.globLat (F := I.F)
      (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) I.L : Set (Fin I.n → I.E)) := by
  ext u
  simp only [Size.latSet, Set.mem_setOf_eq, SetLike.mem_coe]
  rw [lamAf_eq]
  rfl
end PI.UnitaryGroupMassFormula.LSC.LatIs
