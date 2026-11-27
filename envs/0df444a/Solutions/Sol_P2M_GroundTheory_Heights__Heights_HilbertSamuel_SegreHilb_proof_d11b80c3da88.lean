-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_SegreHilb_proof_d11b80c3da88
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:58:06.916447+00:00
-- url     : https://prove2.me/submissions/0946cf7f-bfb5-4456-9812-a2a8175503a0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegreHilb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSegreHilb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  (F : Type) [Field F]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace SegreHilb
theorem _root_.solution : SegreHilb.Statement := by
  intro F _ K _ _ _ ι _ q n
  unfold hilbFn
  by_cases hn : 0 ≤ n
  · rw [if_pos (fun _ => hn), if_pos (fun _ => hn)]
    exact congrArg (fun x : ℕ => (x : ℤ)) (segreGradedPieceEquiv F q n.toNat).finrank_eq
  · rw [if_neg (fun h => hn (h ())), if_neg (fun h => hn (h (Classical.arbitrary K)))]
end SegreHilb
end GroundTheory.Heights₂.Heights.HilbertSamuel
