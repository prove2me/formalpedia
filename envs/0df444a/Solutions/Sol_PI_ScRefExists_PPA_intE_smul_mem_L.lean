-- Prove2me | solution 1 for PI.ScRefExists.PPA.intE_smul_mem_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:20:39.250825+00:00
-- url     : https://prove2.me/submissions/b622c819-30da-40ca-adb7-ff29cc327aae

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_NatCastSmulMemL
import Theorems.Thm_PI_ScRefExists_PPA_oE_smul

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
open PI PI.ScRefExists PI.ScRefExists.PPA
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.PPA
theorem _root_.solution (a : 𝓞 I.E) {x : Fin I.n → I.E} (hx : x ∈ I.L) : (a : I.E) • x ∈ I.L := by
  rw [← oE_smul]
  exact I.L.smul_mem a hx
end PI.ScRefExists.PPA
