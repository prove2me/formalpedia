-- Prove2me | solution 1 for PI.ScRefExists.Id.iE_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:25:23.295116+00:00
-- url     : https://prove2.me/submissions/1590b58c-4cf7-4c4c-875c-61dc63b21814

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemLiftOfSteps
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemTen
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
theorem _root_.solution (θ : 𝓞 I.E) : iE I (θ : I.E) ∈ IntAf I.F I.E := by
  rw [iE_apply]
  exact Subring.subset_closure (Or.inl ⟨⟨(θ : I.E), θ, rfl⟩, rfl⟩)
end PI.ScRefExists.Id
