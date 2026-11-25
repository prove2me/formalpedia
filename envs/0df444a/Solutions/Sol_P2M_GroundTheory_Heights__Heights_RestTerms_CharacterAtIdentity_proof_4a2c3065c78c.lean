-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CharacterAtIdentity_proof_4a2c3065c78c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:42:14.855689+00:00
-- url     : https://prove2.me/submissions/dc4b1f31-3d6d-4ddb-a7f0-30dc84c3aa74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCharacterAtIdentity
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_symmetricGroupCharacter_eq_cf_ddc4362c6d08

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
namespace CharacterAtIdentity
theorem _root_.solution (h1 : CombTableEqWords.Statement)
    (h2 : CombCfAtStair.Statement) : CharacterAtIdentity.Statement := by
  intro m lam hlam
  rw [symmetricGroupCharacter_eq_cf, h2 m (∑ i, lam i) lam hlam, h1 m lam hlam]
end CharacterAtIdentity
end GroundTheory.Heights₂.Heights.RestTerms
