-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_ScXuExists_vecV_smul__5475ffa01793
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:35:48.471905+00:00
-- url     : https://prove2.me/submissions/2d2ccfae-97c4-4585-9e9d-705d281c9990

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_CompactLocalGlobal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (a : I.E ⊗[I.F] Af I.F)
    (x : Fin I.n → I.E ⊗[I.F] Af I.F) :
    PI.FinKW.vecV I v (a • x) = PI.FinKW.psiV I v a • PI.FinKW.vecV I v x := by
  funext i
  simp only [PI.FinKW.vecV, Pi.smul_apply, smul_eq_mul, map_mul]
end PI.UnitaryGroupMassFormula.ScXuExists
