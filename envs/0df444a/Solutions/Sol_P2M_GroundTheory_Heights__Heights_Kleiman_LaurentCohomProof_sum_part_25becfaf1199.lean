-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_sum_part_25becfaf1199
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:02:21.013008+00:00
-- url     : https://prove2.me/submissions/8974dc43-756d-4def-9e8c-d8ebacfde30b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurentCohom
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_apply_c050aba19709

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
variable {S : Type u} [CommRing S] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
theorem _root_.solution (f : Laurent S N) : ∑ J, part S J f = f := by
  ext a
  rw [Finsupp.finsetSum_apply]
  simp only [part_apply]
  rw [Finset.sum_ite_eq]
  simp
end GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
