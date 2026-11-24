-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.BrB.sigV_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:37:17.572423+00:00
-- url     : https://prove2.me/submissions/b28e6788-9d55-4ece-9b2a-459280504ca6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondProjectionSplitEquiv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorNsmul
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.BrB
open NumberField IsDedekindDomain Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists.BrB
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : KV I v) :
    sigV I v (algebraMap (KV I v) (RV I v) c) = algebraMap (KV I v) (RV I v) c := by
  simp [sigV, Algebra.TensorProduct.algebraMap_apply]
end PI.UnitaryGroupMassFormula.ScXuExists.BrB
