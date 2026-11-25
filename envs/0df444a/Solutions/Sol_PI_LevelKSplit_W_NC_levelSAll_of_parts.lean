-- Prove2me | solution 1 for PI.LevelKSplit.W.NC.levelSAll_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:39:10.540567+00:00
-- url     : https://prove2.me/submissions/af27d36b-b85a-451a-980e-f9c9295412f2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemidirectExistsOfParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ConjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjHA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_FiniteAdelesSecondCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MeasAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Theorems.Thm_PI_LevelKSplit_W_NC_conjNHAll_of
import Theorems.Thm_PI_LevelKSplit_W_ExS_existSAll_of
import Theorems.Thm_PI_LevelKSplit_W_MeasAll_levelSAll_of_exist
import Theorems.Thm_PI_VolSemiDirect_W_product_haar_measure_holds


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
open PI.LevelKSplit.W.ExS PI.LevelKSplit.W.CD
open scoped TensorProduct
namespace PI.LevelKSplit.W.NC
theorem _root_.solution (hS : SemiNHSAll) (hC : NCoordAll) (hV : ModVAll) (hA : NCAsmAll) :
    PI.LevelKSplit.LevelSAll :=
  PI.LevelKSplit.W.MeasAll.levelSAll_of_exist
    (PI.LevelKSplit.W.ExS.existSAll_of PI.VolSemiDirect.W.product_haar_measure_holds (fun _ _ _ => inferInstance) hS
      (conjNHAll_of hC hV hA))
end PI.LevelKSplit.W.NC
