-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiT.semidirect_topological_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:23:38.269247+00:00
-- url     : https://prove2.me/submissions/87e6d330-c142-4ff9-8efd-db825163e621

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulInvPiGMemN
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemidirectExistsOfParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiTop
import Theorems.Thm_PI_LevelKSplit_W_SemiT_semi_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.LevelKSplit.W.SemiA PI.VolSemiDirect.W
open scoped TensorProduct
namespace PI.LevelKSplit.W.SemiT
theorem _root_.solution : PI.LevelKSplit.W.ExS.SemiNHSAll := by
  unfold PI.LevelKSplit.W.ExS.SemiNHSAll PI.LevelKSplit.ForAllCM PI.LevelKSplit.W.ExS.SemiNHS
  intro F E _ _ _ _ _ σ _ M J _ hJ hσσ r P T hP
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact semi_gen hσσ hJ hP
end PI.LevelKSplit.W.SemiT
