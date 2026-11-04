-- Prove2me | solution 1 for ThreeSum.LightBlockSourceRetainedStages.source_eq_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:25:53.660115+00:00
-- url     : https://prove2.me/submissions/88370918-eea1-4044-94ac-e14a74456797

import Definitions.Def_Submission_ThreeSum_LightSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
import Theorems.Thm_ThreeSum_LightBlockSourceBuild_left_value


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceRetainedStages
open Light BlockEncoding BlockIndex BlockSourceEncoding GlobalEncoding
open SubsetAddress LightBlockSourceBuild
set_option maxHeartbeats 1800000
namespace ThreeSum.LightBlockSourceRetainedStages
theorem _root_.solution {β : Type*} [Fintype β] [DecidableEq β]
    {h J N : ℕ} (p : ℕ) (B : Finset β) (b : β → ℤ)
    (q : GlobalOutput h J) (v : ℕ → ℤ) (e : Fin N ≃ B)
    (hinput : ∀ i : Fin N, v i.val = b (e i)) :
    LightSourceRetainedStages.source (modulus h J)
      (fun S => endpointLeft (outputOccurrences q) (unindexSet S))
      (fun S => if LeftAllowed (outputOccurrences q) (unindexSet S) then 1 else 0)
      (histogram p (modulus h J) 0 v N) = BlockIndexedQuery.leftSource (p : ℤ) B b q := by
  funext S
  exact congrArg (fun n : ℕ => (n : ℤ))
    (left_value (outputOccurrences q) p B b (fun _ => unindexSet S) v e hinput 0)
end ThreeSum.LightBlockSourceRetainedStages
