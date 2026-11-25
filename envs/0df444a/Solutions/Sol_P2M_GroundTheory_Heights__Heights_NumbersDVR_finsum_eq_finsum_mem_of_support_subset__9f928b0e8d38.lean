-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_finsum_eq_finsum_mem_of_support_subset__9f928b0e8d38
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:23.260425+00:00
-- url     : https://prove2.me/submissions/f89dd9ab-9458-4986-b7e5-8e2273b20b82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalCorresp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {α : Type*} (f : α → ℤ) {s : Set α}
    (h : Function.support f ⊆ s) : ∑ᶠ i, f i = ∑ᶠ i ∈ s, f i := by
  rw [finsum_mem_def, Set.indicator_eq_self.2 h]
end GroundTheory.Heights₂.Heights.NumbersDVR
