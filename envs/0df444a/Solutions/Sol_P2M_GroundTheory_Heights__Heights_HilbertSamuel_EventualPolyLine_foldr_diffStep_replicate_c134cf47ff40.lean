-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_foldr_diffStep_replicate_c134cf47ff40
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:55:22.831777+00:00
-- url     : https://prove2.me/submissions/ef3b6457-6b9d-42eb-8e0a-8678fdc17716

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolyLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolyLine

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
open Polynomial GroundTheory.Heights₂.Heights.NumbersDVR fwdDiff
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine
variable {K : Type}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine
theorem _root_.solution (a : K → ℤ) (f : (K → ℤ) → ℤ) (n : ℕ) (x : K → ℤ) :
    (List.replicate n a).foldr diffStep f x = (fwdDiff a)^[n] f (x - n • a) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have e1 : x - (n + 1) • a + a = x - n • a := by rw [succ_nsmul]; abel
    have e2 : x - a - n • a = x - (n + 1) • a := by rw [succ_nsmul]; abel
    rw [List.replicate_succ, List.foldr_cons, Function.iterate_succ_apply']
    show (List.replicate n a).foldr diffStep f x - (List.replicate n a).foldr diffStep f (x - a) = _
    rw [ih, ih, e2]
    show _ = (fwdDiff a)^[n] f (x - (n + 1) • a + a) - (fwdDiff a)^[n] f (x - (n + 1) • a)
    rw [e1]
end GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine
