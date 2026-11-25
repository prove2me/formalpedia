-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_hypotheses_inhabited_9c9f063d7484
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:55:40.088116+00:00
-- url     : https://prove2.me/submissions/5f5d4446-4769-45b3-b79a-f1e783e3fa24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports

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
namespace GroundTheory.Heights₂.Heights
namespace GenericLinearTrdeg
theorem _root_.solution :
    Algebra.trdeg ℚ (Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 => (1 : ℚ)))) = ((0 : ℕ) : Cardinal) := by
  rw [Nat.cast_zero, trdeg_eq_zero_iff]
  infer_instance
end GenericLinearTrdeg
end GroundTheory.Heights₂.Heights
