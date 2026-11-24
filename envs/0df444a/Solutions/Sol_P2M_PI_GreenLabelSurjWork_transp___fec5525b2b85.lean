-- Prove2me | solution 1 for P2M_PI_GreenLabelSurjWork_transp___fec5525b2b85
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:10.968705+00:00
-- url     : https://prove2.me/submissions/e63cc96a-874a-4bfe-9f9b-83588c71af0c

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
theorem _root_.solution (e : ι ≃ κ) (τ : FDRep ℂ (GL ι K)) (g : GL κ K) :
    (transp e τ).ρ g = τ.ρ ((glEquiv K e).symm g) := rfl
end PI.GreenLabelSurjWork
