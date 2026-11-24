-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_exists_perm_strictAnti_2971ced7b813
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:22:16.200526+00:00
-- url     : https://prove2.me/submissions/eebe5206-ae0d-4ec6-b31f-a966cae2e404

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
variable {m : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.Comb
theorem _root_.solution {u : Fin m → ℕ} (hu : Function.Injective u) :
    ∃ σ : Perm (Fin m), StrictAnti (u ∘ σ) := by
  have hmono : StrictMono (u ∘ Tuple.sort u) :=
    (Tuple.monotone_sort u).strictMono_of_injective (hu.comp (Tuple.sort u).injective)
  refine ⟨Fin.revPerm.trans (Tuple.sort u), fun a b hab => ?_⟩
  have := hmono (Fin.rev_lt_rev.mpr hab)
  simpa using this
end GroundTheory.Heights₂.Heights.RestTerms.Comb
