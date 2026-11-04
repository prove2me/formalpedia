-- Prove2me | solution 1 for ThreeSum.TrimScales.vertexLoad_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:10:54.953802+00:00
-- url     : https://prove2.me/submissions/d1770b5d-66c9-4ee3-ae1c-e1c2cafd4939

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos


set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.TrimScales
theorem _root_.solution (h : ℕ) : 0 < vertexLoad h := by
  have hV : (0 : ℝ) < LocalCoverBounds.vertexCount (512 * h) h := by
    exact_mod_cast (Nat.choose_pos (by omega : h ≤ 512 * h))
  have hp : (0 : ℝ) < LocalCoverBounds.localPrime h := by
    exact_mod_cast LocalCoverBounds.localPrime_pos h
  exact div_pos hV hp
end ThreeSum.TrimScales
