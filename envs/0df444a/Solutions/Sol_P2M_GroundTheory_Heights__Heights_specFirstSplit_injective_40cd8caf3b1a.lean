-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_specFirstSplit_injective_40cd8caf3b1a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:40:09.3388+00:00
-- url     : https://prove2.me/submissions/661d46c1-0417-4eb6-9b15-979d2617dd69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PSpecFirstNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {F : Type} [Field F] {k n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : Function.Injective (specFirstSplit (k := k) (n := n)) := by
  rintro ⟨i, m⟩ ⟨j, m'⟩ h
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp_all [specFirstSplit]
end GroundTheory.Heights₂.Heights
