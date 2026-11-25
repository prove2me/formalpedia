-- Prove2me | solution 1 for PI.ScRefExists.Id.sig_iA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:26:30.22112+00:00
-- url     : https://prove2.me/submissions/db4b9bd6-2a7c-4f78-bceb-d852cfeaf794

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemLiftOfSteps
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemTen
import Theorems.Thm_PI_ScRefExists_Id_iA_apply

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
theorem _root_.solution (x : Af I.F) : sigA I (iA I x) = iA I x := by
  rw [iA_apply]
  show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) ((1 : I.E) ⊗ₜ[I.F] x) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl
end PI.ScRefExists.Id
