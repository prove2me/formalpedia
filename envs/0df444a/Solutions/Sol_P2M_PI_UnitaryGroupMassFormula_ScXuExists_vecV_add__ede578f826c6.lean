-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_ScXuExists_vecV_add__ede578f826c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:48:17.233715+00:00
-- url     : https://prove2.me/submissions/51e98000-2285-4218-9932-3dcfd0d7eeef

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
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x y : Fin I.n → I.E ⊗[I.F] Af I.F) :
    PI.FinKW.vecV I v (x + y) = PI.FinKW.vecV I v x + PI.FinKW.vecV I v y := by
  funext i
  simp only [PI.FinKW.vecV, Pi.add_apply, map_add]
end PI.UnitaryGroupMassFormula.ScXuExists
