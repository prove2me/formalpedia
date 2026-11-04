-- Prove2me | solution 1 for ThreeSum.LightBlockSourceRetainedStages.source_eq_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:26:36.895519+00:00
-- url     : https://prove2.me/submissions/1f10cd8a-663b-4412-88cd-b5c338da214d

import Definitions.Def_Submission_ThreeSum_LightSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
import Theorems.Thm_ThreeSum_LightBlockSourceBuild_right_value


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceRetainedStages
open Light BlockEncoding BlockIndex BlockSourceEncoding GlobalEncoding
open SubsetAddress LightBlockSourceBuild
set_option maxHeartbeats 1800000
namespace ThreeSum.LightBlockSourceRetainedStages
theorem _root_.solution {β : Type*} [Fintype β] [DecidableEq β]
    {h J N : ℕ} (p : ℕ) (shift : ℤ) (B : Finset β) (b : β → ℤ)
    (q : GlobalOutput h J) (v : ℕ → ℤ) (e : Fin N ≃ B)
    (hinput : ∀ i : Fin N, v i.val = b (e i)) :
    LightSourceRetainedStages.source (modulus h J)
      (fun S => endpointRight (outputOccurrences q) (unindexSet S))
      (fun S => if RightAllowed (outputOccurrences q) (unindexSet S) then 1 else 0)
      (histogram p (modulus h J) shift v N) =
      BlockIndexedQuery.rightSource (p : ℤ) shift B b q := by
  funext S
  exact congrArg (fun n : ℕ => (n : ℤ))
    (right_value (outputOccurrences q) p shift B b (fun _ => unindexSet S) v e hinput 0)
end ThreeSum.LightBlockSourceRetainedStages
