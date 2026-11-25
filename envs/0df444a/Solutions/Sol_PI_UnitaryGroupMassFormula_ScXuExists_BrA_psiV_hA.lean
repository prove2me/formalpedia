-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.BrA.psiV_hA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:43:03.888523+00:00
-- url     : https://prove2.me/submissions/dbe36401-42aa-4935-a712-80d0e13cbdb0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorMemSpan
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_FinKW_LocTo_psiV_inclE
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_psiV_inclE
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_psiV_sigR
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.BrA
open NumberField IsDedekindDomain Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists.BrA
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x y : VA I) :
    PI.FinKW.psiV I v (hA I x y) = hl I v (PI.FinKW.vecV I v x) (PI.FinKW.vecV I v y) := by
  simp only [hA, hl, Formalism.UG.hform, map_sum, map_mul, Matrix.map_apply, psiV_sigR, psiV_inclE,
    PI.FinKW.vecV]
end PI.UnitaryGroupMassFormula.ScXuExists.BrA
