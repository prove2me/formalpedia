-- Prove2me | solution 1 for PI.GreenLabelSurjWork.glEquiv_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:58.948268+00:00
-- url     : https://prove2.me/submissions/33ee66c2-7289-4ad7-9445-c2d71bfb6403

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
open PI PI.GreenLabelSurjWork
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace PI.GreenLabelSurjWork
theorem _root_.solution (e : ι ≃ κ) (g : GL ι K) :
    ((glEquiv K e g : GL κ K) : Matrix κ κ K) = Matrix.reindex e e (g : Matrix ι ι K) := rfl
end PI.GreenLabelSurjWork
