-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_L4_lowIm_keep__abc410c6108a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:45:34.295072+00:00
-- url     : https://prove2.me/submissions/5312ae0b-3038-4cdc-a646-6fdcc94b7cd3

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j : ℕ) (ρ : Fin r)
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x, A (glAct p LL j c d x) = glAct p LL j c d (A x)) :
    ∀ x ∈ lowIm' p LL j ρ, A x ∈ lowIm' p LL j ρ := by
  have key : lowIm' p LL j ρ ≤ (lowIm' p LL j ρ).comap A := by
    unfold lowIm'
    refine iSup_le fun c => iSup_le fun d => iSup_le fun hcd => ?_
    rintro y ⟨z, -, rfl⟩
    rw [Submodule.mem_comap, hA c hcd.1 d hcd.2.1 z]
    exact Submodule.mem_iSup_of_mem c (Submodule.mem_iSup_of_mem d
      (Submodule.mem_iSup_of_mem hcd ⟨A z, Submodule.mem_top, rfl⟩))
  intro x hx
  exact key hx
end Formalism.InvariantFactorPaths.L4
