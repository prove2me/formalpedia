-- Prove2me | solution 1 for PI.ScRefExists.WF.mem_LA_of_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:23:27.081649+00:00
-- url     : https://prove2.me/submissions/ba1d8b4f-2e66-4b2b-a9b3-bee92cf0afdd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_StarMemAp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_MemLAOfNsmul
import Theorems.Thm_PI_ScRefExists_WF_mem_LA_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open PI PI.ScRefExists PI.ScRefExists.WF
variable {I : Formalism.MainNotions.S.AutInst} {p : ℕ}
namespace PI.ScRefExists.WF
theorem _root_.solution (hp : p.Prime) {M : ℕ} (hM : Nat.Coprime M p) {x : Fin I.n → I.E}
    (hx : M • x ∈ I.L) : x ∈ LA I p := by
  refine (mem_LA_iff hp).2 ⟨M, hM, ?_⟩
  rwa [← Nat.cast_smul_eq_nsmul I.E] at hx
end PI.ScRefExists.WF
