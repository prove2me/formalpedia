-- Prove2me | solution 1 for PI.ScRefExists.WF.hG_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:21:09.25037+00:00
-- url     : https://prove2.me/submissions/d4f781e1-1eb3-4c93-abac-139436c572a5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_StarMemAp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_MemLAOfNsmul

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
theorem _root_.solution {x y : Fin I.n → I.E} (hx : x ∈ I.L) (hy : y ∈ I.L) :
    hG I x y ∈ (algebraMap (𝓞 I.E) I.E).range := by
  unfold hG
  exact (I.L_dual y).mp hy x hx
end PI.ScRefExists.WF
