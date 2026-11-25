-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.BrA.first_coordinate_vector_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:42:28.516483+00:00
-- url     : https://prove2.me/submissions/eea04ff6-446d-4df1-9247-d9884bb78f8f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorMemSpan
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_alg_eq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_FinKW_LocTo_ov_smul_vec
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
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (p1 : RV I v →+* KV I v)
    (hp : ∀ c : KV I v, p1 (algebraMap (KV I v) (RV I v) c) = c) (c : OV I v) (X : Fin I.n → RV I v) :
    vec1 p1 (c • X) = c • vec1 p1 X := by
  rw [PI.FinKW.LocTo.ov_smul_vec]
  funext i
  simp only [vec1, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← alg_eq, hp]
  rfl
end PI.UnitaryGroupMassFormula.ScXuExists.BrA
