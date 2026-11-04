-- Prove2me | solution 1 for ThreeSum.MassScales.falseNumerator_eventually_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:09:26.892367+00:00
-- url     : https://prove2.me/submissions/374daed7-a4dc-4297-b895-1a7c6f6f7759

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
import Theorems.Thm_ThreeSum_MassScales_rawTripleBound_pos
import Theorems.Thm_ThreeSum_MassScales_scoreLoss_pos
import Theorems.Thm_ThreeSum_MassScales_primeLoss_pos
import Theorems.Thm_ThreeSum_MassScales_candidateCount_eventually_pos

set_option autoImplicit false
open ThreeSum ThreeSum.MassScales
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.MassScales
theorem _root_.solution (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, 0 < falseNumerator k n := by
  filter_upwards [candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
  have ht := rawTripleBound_pos (by omega : 0 < n)
  have hs := scoreLoss_pos k n
  have hp := primeLoss_pos n
  unfold falseNumerator
  positivity
end ThreeSum.MassScales
