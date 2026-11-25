-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutTransportLast_lastEquiv_bottom_671ead235411
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:52.919451+00:00
-- url     : https://prove2.me/submissions/e9ba4373-5fbd-4b0d-84f2-f3a0c1185c55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutTransportLast

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
open GroundTheory.Heights₂.Heights.RestCutTransportLast
namespace GroundTheory.Heights₂.Heights.RestCutTransportLast
theorem _root_.solution (j k : ℕ) (i : Fin k) (h : j + (i : ℕ) < k + j) :
    restLastEquiv j k ⟨j + i, h⟩ = Sum.inr i := by
  have : (finCongr (Nat.add_comm k j)) ⟨j + i, h⟩ = Fin.natAdd j i := Fin.ext rfl
  simp only [restLastEquiv, Equiv.trans_apply, this, finSumFinEquiv_symm_apply_natAdd]
end GroundTheory.Heights₂.Heights.RestCutTransportLast
