-- Prove2me | solution 1 for PI.FT.cT_map_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:05.304784+00:00
-- url     : https://prove2.me/submissions/a7a448e0-faf0-43f2-b5ec-d6833da10ab9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_StepTransl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff

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
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
variable (R : Type) [CommRing R] [Algebra F R]
namespace PI.FT
theorem _root_.solution {m n : ℕ} (a : Matrix (Fin m) (Fin n) E) :
    (Formalism.UG.cT (σ : E →+* E) a).map (inclR (F := F) (E := E) R) =
      Formalism.UG.cT (sigR R σ) (a.map (inclR (F := F) (E := E) R)) := by
  ext i j
  simp [Formalism.UG.cT, inclR, sigR]
end PI.FT
