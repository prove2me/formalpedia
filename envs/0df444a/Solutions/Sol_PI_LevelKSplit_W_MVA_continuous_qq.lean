-- Prove2me | solution 1 for PI.LevelKSplit.W.MVA.continuous_qq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:51:32.10549+00:00
-- url     : https://prove2.me/submissions/13bbdd01-0569-4c00-93d4-8e19058c0da1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MapFstConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousFirstOrbitMap
import Theorems.Thm_PI_LevelKSplit_W_MVA_continuous_crd
import Theorems.Thm_PI_LevelKSplit_W_MVA_continuous_crd_symm

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
namespace PI.LevelKSplit.W.MVA
theorem _root_.solution :
    Continuous (fun y : (R1 ⊗[F] E) × (R2 ⊗[F] E) => qq R1 R2 y.1 y.2) := by
  delta qq
  exact (continuous_crd_symm (R1 × R2)).comp (continuous_pi fun k =>
    (((continuous_apply k).comp (continuous_crd R1)).comp continuous_fst).prodMk
      (((continuous_apply k).comp (continuous_crd R2)).comp continuous_snd))
end PI.LevelKSplit.W.MVA
