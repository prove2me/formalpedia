-- Prove2me | solution 1 for PI.LevelKSplit.W.MVA.continuous_crd_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:51:54.898827+00:00
-- url     : https://prove2.me/submissions/3718e530-b279-4261-8c93-794a3e4e286c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MapFstConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousFirstOrbitMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.MVA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
namespace PI.LevelKSplit.W.MVA
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] : Continuous (crd (F := F) (E := E) R).symm := by
  first
  | exact continuous_induced_rng.2 (by simpa [Function.comp_def] using continuous_id)
  | exact IsModuleTopology.continuous_of_linearMap (crd (F := F) (E := E) R).symm.toLinearMap
  | fun_prop
end PI.LevelKSplit.W.MVA
