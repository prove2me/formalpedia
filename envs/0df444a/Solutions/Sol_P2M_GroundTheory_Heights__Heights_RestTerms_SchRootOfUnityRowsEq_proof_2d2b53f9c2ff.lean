-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchRootOfUnityRowsEq_proof_2d2b53f9c2ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:54:34.810506+00:00
-- url     : https://prove2.me/submissions/958dd2f7-e7fd-4df8-94ff-24d77f797d24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchRootOfUnityRowsEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootOfUnity_pow_mod_be4eb14082ec

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
open Complex
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchRootOfUnityRowsEq
theorem _root_.solution : SchRootOfUnityRowsEq.Statement := by
  intro k l i i' hne hmod
  have hk : k ≠ 0 := by
    rintro rfl
    exact i.elim0
  apply Matrix.det_zero_of_row_eq hne
  funext j
  simp only [Matrix.of_apply]
  rw [pow_mul', pow_mul', rootOfUnity_pow_mod k hk (l i), rootOfUnity_pow_mod k hk (l i'), hmod]
end SchRootOfUnityRowsEq
end GroundTheory.Heights₂.Heights.RestTerms
