-- Prove2me | solution 1 for PI.ScRefExists.Id.iA_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:20:11.122006+00:00
-- url     : https://prove2.me/submissions/79c8f2fd-fd2b-4b61-8cc2-37042f986ca0

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
theorem _root_.solution {x : Af I.F} (hx : x ∈ Formalism.UG.intAd I.F) : iA I x ∈ IntAf I.F I.E := by
  rw [iA_apply]
  exact Subring.subset_closure (Or.inr ⟨⟨x, hx⟩, rfl⟩)
end PI.ScRefExists.Id
