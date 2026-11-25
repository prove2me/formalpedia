-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameMultiHomog_proof_0a47e7848016
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:03:07.907878+00:00
-- url     : https://prove2.me/submissions/411be3d6-13c4-46f0-9457-f420ddde8835

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_mapDomain_blockWeight_c47dcb6e8590

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace RenameMultiHomog
theorem _root_.solution : RenameMultiHomog.Statement.{u} := by
  intro R _ K K' _ _ j ι ι' g hg f d hf e he
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero g f e he
  rw [weight_mapDomain_blockWeight j ι ι' g hg u, hf hu]
end RenameMultiHomog
end GroundTheory.Heights₂.Heights.FieldNumbers
