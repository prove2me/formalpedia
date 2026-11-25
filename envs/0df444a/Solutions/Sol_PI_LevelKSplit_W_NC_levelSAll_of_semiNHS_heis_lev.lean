-- Prove2me | solution 1 for PI.LevelKSplit.W.NC.levelSAll_of_semiNHS_heis_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:30:56.473803+00:00
-- url     : https://prove2.me/submissions/84b8a22f-9785-4cd7-94c2-50cc72130327

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_CoordinateHomeomorphism
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOfSemiNHSHeisLev
import Theorems.Thm_PI_LevelKSplit_W_NC_ncoordAll_of
import Theorems.Thm_PI_LevelKSplit_W_NC_levelSAll_of_parts


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
namespace PI.LevelKSplit.W.NC
theorem _root_.solution (hS : PI.LevelKSplit.W.ExS.SemiNHSAll) (hH : HeisPAll) (hL : LevPAll)
    (hV : PI.LevelKSplit.W.CD.ModVAll) (hA : NCAsmAll) : PI.LevelKSplit.LevelSAll :=
  levelSAll_of_parts hS (ncoordAll_of hH hL) hV hA
end PI.LevelKSplit.W.NC
