-- Prove2me | solution 1 for PI.ScRefExists.Id.iE_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:20:15.259923+00:00
-- url     : https://prove2.me/submissions/5878564c-f555-415f-a2fc-e038e4b213a5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemLiftOfSteps
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemTen
import Theorems.Thm_PI_ScRefExists_Id_iA_apply
import Theorems.Thm_PI_ScRefExists_Id_iE_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.Id
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.Id
theorem _root_.solution (x : I.F) : iE I (algebraMap I.F I.E x) = iA I (algebraMap I.F (Af I.F) x) := by
  rw [iE_apply, iA_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    TensorProduct.smul_tmul]
end PI.ScRefExists.Id
