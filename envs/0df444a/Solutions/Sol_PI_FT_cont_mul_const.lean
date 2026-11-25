-- Prove2me | solution 1 for PI.FT.cont_mul_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:08.916573+00:00
-- url     : https://prove2.me/submissions/c639bcb7-9d03-4b93-9e33-65b0bcdb3258

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_InstIsModTopTens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
namespace PI.FT
theorem _root_.solution (c d : R ⊗[F] E) : Continuous (fun a : R ⊗[F] E => c * a * d) := by
  refine (IsModuleTopology.continuous_of_linearMap (R := R)
    ((LinearMap.mulRight R d).comp (LinearMap.mulLeft R c))).congr fun a => ?_
  simp
end PI.FT
