-- Prove2me | solution 1 for PI.LevelKSplit.W.MVA.continuous_psiE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:10:31.054252+00:00
-- url     : https://prove2.me/submissions/c56f38c7-1f31-4381-baea-4ffeef78e02e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MapFstConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousFirstOrbitMap
import Theorems.Thm_PI_LevelKSplit_W_MVA_continuous_first_orbit_map
import Theorems.Thm_PI_LevelKSplit_W_MVA_continuous_p2

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
theorem _root_.solution : Continuous (psiE (F := F) (E := E) (M := M) R1 R2) := by
  show Continuous (fun x : Fin M → (R1 × R2) ⊗[F] E =>
    (fun i => p1 (F := F) (E := E) R1 R2 (x i), fun i => p2 (F := F) (E := E) R1 R2 (x i)))
  exact (continuous_pi fun i => (continuous_first_orbit_map R1 R2).comp (continuous_apply i)).prodMk
    (continuous_pi fun i => (continuous_p2 R1 R2).comp (continuous_apply i))
end PI.LevelKSplit.W.MVA
