-- Prove2me | solution 1 for ThreeSum.BandRawA.allProducts_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:25.716285+00:00
-- url     : https://prove2.me/submissions/d9037e95-c4cb-4867-a328-dbe6c3805803

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Theorems.Thm_ThreeSum_BandRawA_bandPositions_lt
import Definitions.Def_WeightedCache3SUM_Alias_8fa29246dc9d5286


set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
namespace ThreeSum.BandRawA
theorem _root_.solution {nA nB nC g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ allProducts nA nB nC g rs) :
    t.1 < (items nA g rs).length ∧ t.2.1 < nB ∧ t.2.2 < nC := by
  obtain ⟨ha,hb,hc⟩ := mem_allProducts.mp ht
  exact ⟨ha,bandPositions_lt hb,bandPositions_lt hc⟩
end ThreeSum.BandRawA
