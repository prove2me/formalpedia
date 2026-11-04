-- Prove2me | solution 1 for ThreeSum.BruteTripleIndex.hit_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:07:10.381015+00:00
-- url     : https://prove2.me/submissions/2f6ccc5c-bff2-4c15-96b8-60dd9f1f4c49

import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSum_BruteTripleIndex

set_option autoImplicit false
open ThreeSum ThreeSum.BruteTripleIndex
namespace ThreeSum.BruteTripleIndex
theorem _root_.solution {n : ℕ} (x : Fin n → ℤ) (hn : 0 < n) : ¬ Hit x hn 0 := by
  rintro ⟨_,_,hlt,_⟩
  omega
end ThreeSum.BruteTripleIndex
