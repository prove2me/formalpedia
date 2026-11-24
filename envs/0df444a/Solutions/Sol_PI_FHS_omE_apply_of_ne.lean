-- Prove2me | solution 1 for PI.FHS.omE_apply_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:40.863903+00:00
-- url     : https://prove2.me/submissions/da73c13a-fae5-4bf1-8f7f-52b3345df07a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_ConjTransposeOneKronecker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix FockH1Action
open PI PI.FHS
variable {p q r s : ℕ}
namespace PI.FHS
theorem _root_.solution {l l' : Ln p q r s} (h : l ≠ l') (P : Pol p q r s) :
    omE l l' P = raiB l (lowB l' P) := by
  rw [FockH1Action.omE, if_neg h, add_zero]; rfl
end PI.FHS
