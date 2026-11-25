-- Prove2me | solution 1 for PI.ScRefExists.WF.natsmul_mem_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:55.744736+00:00
-- url     : https://prove2.me/submissions/d026c8ea-3bbd-46e6-a835-e7c9c0a450e2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_StarMemAp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_MemLAOfNsmul
import Theorems.Thm_PI_ScRefExists_WF_osmul
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
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open PI PI.ScRefExists PI.ScRefExists.WF
variable {I : Formalism.MainNotions.S.AutInst} {p : ℕ}
namespace PI.ScRefExists.WF
theorem _root_.solution {s : ℕ} {x : Fin I.n → I.E} (hx : x ∈ I.L) : (s : I.E) • x ∈ I.L := by
  have h1 : ((s : 𝓞 I.E) : I.E) = (s : I.E) := by simp
  rw [← h1, ← osmul]
  exact I.L.smul_mem _ hx
end PI.ScRefExists.WF
