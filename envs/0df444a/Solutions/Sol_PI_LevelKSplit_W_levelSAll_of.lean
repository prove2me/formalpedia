-- Prove2me | solution 1 for PI.LevelKSplit.W.levelSAll_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:02:47.486533+00:00
-- url     : https://prove2.me/submissions/e199b91b-ac90-4e53-8df5-3360800c5ab0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LevelKSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf
import Theorems.Thm_PI_LevelKSplit_W_levelS_of
import Theorems.Thm_PI_LevelKSplit_W_sig_invol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct
namespace PI.LevelKSplit.W
theorem _root_.solution (h1 : ExistSAll) (h2 : MeasKfAll) (h3 : SplitKAll) : LevelSAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  exact levelS_of (sig_invol hσ) (h1 F E σ hσ M J hJ) (h2 F E σ hσ M J hJ) (h3 F E σ hσ M J hJ)
end PI.LevelKSplit.W
