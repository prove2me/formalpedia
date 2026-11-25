-- Prove2me | solution 1 for PI.ScRefExists.WF.hG_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:59:53.300026+00:00
-- url     : https://prove2.me/submissions/e02a9cce-fae7-44dc-8b3b-85afbec84bf0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_StarMemAp
import Theorems.Thm_PI_ScRefExists_WF_hG_single

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
open Matrix
open PI PI.ScRefExists PI.ScRefExists.WF
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.WF
theorem _root_.solution (v : Fin I.n → I.E) (h : ∀ x, hG I x v = 0) : v = 0 := by
  have h1 : I.J *ᵥ v = 0 := funext fun i => by
    rw [← hG_single I i v]
    exact h _
  exact Matrix.eq_zero_of_mulVec_eq_zero I.J_det h1
end PI.ScRefExists.WF
