-- Prove2me | solution 1 for PI.FT.map_one_incl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:08.897178+00:00
-- url     : https://prove2.me/submissions/31b36657-d96b-4027-b37e-72352602022c

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
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] :
    (1 : Matrix n n E).map (inclR (F := F) (E := E) R) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
end PI.FT
