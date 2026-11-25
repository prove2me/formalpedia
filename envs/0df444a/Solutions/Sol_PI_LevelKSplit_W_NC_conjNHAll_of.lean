-- Prove2me | solution 1 for PI.LevelKSplit.W.NC.conjNHAll_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:30:54.645798+00:00
-- url     : https://prove2.me/submissions/bd780c80-c1e7-4b85-92f8-ea18f1f90543

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemidirectExistsOfParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ConjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjHA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_FiniteAdelesSecondCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MeasAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs

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
theorem _root_.solution (hC : NCoordAll) (hV : ModVAll) (hA : NCAsmAll) : ConjNHAll := by
  intro F E _ _ _ _ _ σ hCM M J hJ
  exact hA F E σ hCM M J hJ (hC F E σ hCM M J hJ) (hV F E σ hCM M J hJ)
end PI.LevelKSplit.W.NC
