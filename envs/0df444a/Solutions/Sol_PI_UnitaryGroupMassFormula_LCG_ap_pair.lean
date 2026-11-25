-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ap_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:29:40.755052+00:00
-- url     : https://prove2.me/submissions/a2fe5354-a63f-4ef8-a406-33f51358fc91

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_QJQ

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
theorem _root_.solution (y : I.GA) (v : InfinitePlace I.F) (p q : Fin I.n → ℂ) :
    star (qM I y v *ᵥ p) ⬝ᵥ (Formalism.REAL.Jm (I.ε v) *ᵥ (qM I y v *ᵥ q)) =
      star p ⬝ᵥ (I.J.map (I.φ v) *ᵥ q) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ap_QJQ]
end PI.UnitaryGroupMassFormula.LCG
