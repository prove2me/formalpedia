-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.vecV_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:43:36.298865+00:00
-- url     : https://prove2.me/submissions/f0fceb54-7f6a-4b4c-8605-1a3daf400764

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_NatCastTmul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_FinKW_LocTo_psiV_inclE
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_psiV_inclE
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (l : Fin I.n → I.E) :
    PI.FinKW.vecV I v (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (l i)) =
      Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l := by
  funext i
  simp only [PI.FinKW.vecV, PI.FinKW.LocTo.psiV_inclE]
  rfl
end PI.UnitaryGroupMassFormula.ScXuExists
