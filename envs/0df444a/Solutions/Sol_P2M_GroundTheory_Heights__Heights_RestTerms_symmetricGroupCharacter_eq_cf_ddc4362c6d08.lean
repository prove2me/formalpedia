-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_symmetricGroupCharacter_eq_cf_ddc4362c6d08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:32:03.784647+00:00
-- url     : https://prove2.me/submissions/b3eb30ab-79ee-4d9c-9091-0a5fc59ff394

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCharacterAtIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset Comb
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution {m : ℕ} (lam : Fin m → ℕ) (rho : List ℕ) :
    symmetricGroupCharacter lam rho =
      cf (fun i => lam i + stair m i) (alternantPsum m rho) := rfl
end GroundTheory.Heights₂.Heights.RestTerms
