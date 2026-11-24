-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_sum_add_pi_single_one_3a9c5801f689
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:45.163334+00:00
-- url     : https://prove2.me/submissions/ab75eccf-6e86-4895-b802-b5326dd8368d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegLTGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegLTGrowth

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
open GroundTheory.Heights₂.Heights.NumbersDVR
variable {K : Type} [Fintype K] [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (m : K → ℕ) (k : K) :
    ∑ j, (m + Pi.single k 1 : K → ℕ) j = ∑ j, m j + 1 := by
  simp [Finset.sum_add_distrib]
end GroundTheory.Heights₂.Heights.HilbertSamuel
