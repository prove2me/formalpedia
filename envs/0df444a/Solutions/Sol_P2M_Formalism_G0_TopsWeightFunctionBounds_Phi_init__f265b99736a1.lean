-- Prove2me | solution 1 for P2M_Formalism_G0_TopsWeightFunctionBounds_Phi_init__f265b99736a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:37:59.624798+00:00
-- url     : https://prove2.me/submissions/afcef9a8-7526-473a-b57d-422243edda5b

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_Phi_init

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution {R L₂ : ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1)
    (hR : 1 ≤ R) (K : ℕ) (ev : Bool) :
    Phi R L₂ δ (init K ev) ≤ (1 - aF L₂ δ ^ R) ^ K := by
  unfold init
  split_ifs with hK
  · subst hK; simp [Phi]
  · exact Phi_init h0 hL hLδ hR (by omega) ev
end Formalism.G0.TopsWeightFunctionBounds
