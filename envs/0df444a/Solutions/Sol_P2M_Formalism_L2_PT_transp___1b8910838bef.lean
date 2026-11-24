-- Prove2me | solution 1 for P2M_Formalism_L2_PT_transp___1b8910838bef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:10:45.691811+00:00
-- url     : https://prove2.me/submissions/967128d7-40a1-4fd5-94e7-27f1e6ce1536

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory
open Formalism Formalism.L2 Formalism.L2.PT
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace Formalism.L2.PT
theorem _root_.solution (e : ι ≃ κ) (τ : FDRep ℂ (GL ι K)) (γ : GL κ K) :
    (transp e τ).ρ γ = τ.ρ ((glEquiv K e).symm γ) := rfl
end Formalism.L2.PT
