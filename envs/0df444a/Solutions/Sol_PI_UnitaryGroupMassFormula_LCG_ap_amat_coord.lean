-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ap_amat_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:56:48.735986+00:00
-- url     : https://prove2.me/submissions/8c3eaab2-b655-4dc0-bab3-91162333f862

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_coordV
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_phv_mulVec
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_AQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution (x y : I.GA) (v : InfinitePlace I.F) (δ : Matrix (Fin I.n) (Fin I.n) I.E)
    (w : Fin I.n → I.E) :
    amat I x y v δ *ᵥ PI.LatCountG.coordV I y v w = PI.LatCountG.coordV I x v (δ *ᵥ w) := by
  rw [ap_coordV, ap_coordV, Matrix.mulVec_mulVec, ap_AQ, ← Matrix.mulVec_mulVec, ap_phv_mulVec]
end PI.UnitaryGroupMassFormula.LCG
