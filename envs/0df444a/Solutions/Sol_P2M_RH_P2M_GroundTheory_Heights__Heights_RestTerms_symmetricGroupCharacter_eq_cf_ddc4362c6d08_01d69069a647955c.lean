-- Prove2me | solution 1 for P2M_RH_P2M_GroundTheory_Heights__Heights_RestTerms_symmetricGroupCharacter_eq_cf_ddc4362c6d08_01d69069a647955c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:55:59.781962+00:00
-- url     : https://prove2.me/submissions/23b34c69-50bf-4b1e-9587-b7d5ae9967f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCharacterBound

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
    symmetricGroupCharacter lam rho = cf (fun i => lam i + stair m i) (alternantPsum m rho) :=
  rfl
end GroundTheory.Heights₂.Heights.RestTerms
