-- Prove2me | solution 1 for PI.LevelKSplit.W.MVA.continuous_crd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:51:51.7191+00:00
-- url     : https://prove2.me/submissions/477d5eee-aaf7-4bef-aedf-7e0e5a4cad05

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
    [IsTopologicalRing R] : Continuous (crd (F := F) (E := E) R) := by
  first
  | exact continuous_induced_dom
  | exact IsModuleTopology.continuous_of_linearMap (crd (F := F) (E := E) R).toLinearMap
  | fun_prop
  | (delta crd; exact LinearMap.continuous_of_finiteDimensional _)
end PI.LevelKSplit.W.MVA
