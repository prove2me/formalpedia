-- Prove2me | solution 1 for PI.LevelKSplit.W.NC.cHomeo_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:30:18.12115+00:00
-- url     : https://prove2.me/submissions/2a43cee6-b206-4abc-9909-68a3513a5726

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCIface
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_CoordinateHomeomorphism

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NC
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Q : Type} [AddCommGroup Q] [TopologicalSpace Q] [ContinuousAdd Q]
variable {N A N1 Z : Subgroup G} {Lev : G → G} {sH : Q → G} {yQ : N1 → Q}
namespace PI.LevelKSplit.W.NC
theorem _root_.solution (H : CoordHyp N A N1 Z Lev sH yQ) (p : A × (Q × Z)) :
    ((cHomeo H p : N) : G) = (p.1 : G) * sH p.2.1 * (p.2.2 : G) := rfl
end PI.LevelKSplit.W.NC
