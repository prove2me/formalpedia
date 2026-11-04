-- Prove2me | solution 1 for ThreeSum.LightBlockSourceStages.source_eq_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:19:49.217199+00:00
-- url     : https://prove2.me/submissions/bbd31360-7eee-4ffe-ab11-cd6b64517e8d

import Definitions.Def_Submission_ThreeSum_LightSourceStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
import Definitions.Def_Submission_ThreeSum_BlockSourceTableLayout
import Definitions.Def_Submission_ThreeSum_LightBlockSourceStages
import Theorems.Thm_ThreeSum_LightBlockSourceBuild_left_value


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceStages
open Light BlockEncoding BlockIndex BlockSourceEncoding GlobalEncoding
open SubsetAddress LightBlockSourceBuild
set_option maxHeartbeats 1800000
namespace ThreeSum.LightBlockSourceStages
theorem _root_.solution {β : Type*} [Fintype β] [DecidableEq β]
    {h J N src : ℕ} (μ : ℕ → ℤ) (p : ℕ) (B : Finset β) (b : β → ℤ)
    (q : GlobalOutput h J) (e : Fin N ≃ B)
    (hinput : ∀ i : Fin N, μ (src+i.val) = b (e i)) :
    LightSourceStages.source μ src N p (modulus h J) 0
      (fun S => endpointLeft (outputOccurrences q) (unindexSet S))
      (fun S => if LeftAllowed (outputOccurrences q) (unindexSet S) then 1 else 0) =
      BlockIndexedQuery.leftSource (p : ℤ) B b q := by
  funext S
  exact congrArg (fun n : ℕ => (n : ℤ))
    (left_value (outputOccurrences q) p B b (fun _ => unindexSet S)
      (fun i => μ (src+i)) e hinput 0)
end ThreeSum.LightBlockSourceStages
