-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_zero_mem_KSet_rankTwo_9c1fdb6b33be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:10:47.052248+00:00
-- url     : https://prove2.me/submissions/d9eef506-2191-403d-accf-2cdb757270a8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
variable (d : IndexData)
namespace GroundTheory.Heights₂.Heights.TheoremB
theorem _root_.solution : (0 : Weight d1) ∈ KSet d1 0 (quarterInverseN d1) := by
  refine ⟨by rw [norm_zero]; norm_num, by simp [gap], ?_, ?_⟩
  · intro τ hτ
    exact absurd (Subsingleton.elim τ 0) hτ
  · rintro τ a b ⟨hab, hbj⟩
    exfalso
    have hb : b.val < 2 := b.isLt
    have hbj' : b.val ≠ 1 := hbj
    omega
end GroundTheory.Heights₂.Heights.TheoremB
