-- Prove2me | solution 1 for PI.LevelKSplit.W.MVA.continuous_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:50:03.029823+00:00
-- url     : https://prove2.me/submissions/20884639-a254-4a04-be54-81ba792b2d90

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
variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]
  [TopologicalSpace R1] [IsTopologicalRing R1] [TopologicalSpace R2] [IsTopologicalRing R2]
variable {M : ℕ}
namespace PI.LevelKSplit.W.MVA
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (g : HA R σ J) :
    Continuous (lin R σ J g) := by
  first
  | exact IsModuleTopology.continuous_of_linearMap ((lin R σ J g).restrictScalars R)
  | exact Continuous.matrix_mulVec continuous_const continuous_id
  | (delta lin; fun_prop)
end PI.LevelKSplit.W.MVA
