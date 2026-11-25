-- Prove2me | solution 1 for PI.ScRefExists.GWG.osmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:19:51.192135+00:00
-- url     : https://prove2.me/submissions/aa675b26-a3bf-4aad-a836-870fd670d3c1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GlobWIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GWGlue

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
open PI PI.ScRefExists PI.ScRefExists.GWG
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.GWG
theorem _root_.solution {t : I.E} (ht : t ∈ (algebraMap (𝓞 I.E) I.E).range) {v : Fin I.n → I.E}
    (hv : v ∈ I.L) : t • v ∈ I.L := by
  obtain ⟨s, rfl⟩ := ht
  rw [algebraMap_smul]
  exact I.L.smul_mem s hv
end PI.ScRefExists.GWG
