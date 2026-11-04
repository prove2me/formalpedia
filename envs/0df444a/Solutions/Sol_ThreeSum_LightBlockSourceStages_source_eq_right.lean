-- Prove2me | solution 1 for ThreeSum.LightBlockSourceStages.source_eq_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:20:25.297765+00:00
-- url     : https://prove2.me/submissions/55cadc76-8c27-4f02-b220-e47b787423ba

import Definitions.Def_Submission_ThreeSum_LightSourceStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
import Definitions.Def_Submission_ThreeSum_BlockSourceTableLayout
import Definitions.Def_Submission_ThreeSum_LightBlockSourceStages
import Theorems.Thm_ThreeSum_LightBlockSourceBuild_right_value


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceStages
open Light BlockEncoding BlockIndex BlockSourceEncoding GlobalEncoding
open SubsetAddress LightBlockSourceBuild
set_option maxHeartbeats 1800000
namespace ThreeSum.LightBlockSourceStages
theorem _root_.solution {β : Type*} [Fintype β] [DecidableEq β]
    {h J N src : ℕ} (μ : ℕ → ℤ) (p : ℕ) (shift : ℤ) (C : Finset β) (c : β → ℤ)
    (q : GlobalOutput h J) (e : Fin N ≃ C)
    (hinput : ∀ i : Fin N, μ (src+i.val) = c (e i)) :
    LightSourceStages.source μ src N p (modulus h J) shift
      (fun S => endpointRight (outputOccurrences q) (unindexSet S))
      (fun S => if RightAllowed (outputOccurrences q) (unindexSet S) then 1 else 0) =
      BlockIndexedQuery.rightSource (p : ℤ) shift C c q := by
  funext S
  exact congrArg (fun n : ℕ => (n : ℤ))
    (right_value (outputOccurrences q) p shift C c (fun _ => unindexSet S)
      (fun i => μ (src+i)) e hinput 0)
end ThreeSum.LightBlockSourceStages
