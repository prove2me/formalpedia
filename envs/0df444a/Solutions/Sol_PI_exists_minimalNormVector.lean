-- Prove2me | solution 1 for PI.exists_minimalNormVector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:24:37.170323+00:00
-- url     : https://prove2.me/submissions/07ae6501-af7f-4cb3-91c6-92ba86dc9884

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinimalLatticeNorm_NormTwoEqOne
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LatMin
import Theorems.Thm_PI_LatMinWork_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI
namespace PI
theorem _root_.solution : PI.LatMin := by
  intro p _ σ B L W hp2 _ _ hL hsm hadd hsym hne
  refine PI.LatMinWork.main hp2 B L hL ?_ hadd hsym hne
  intro c u v
  have h : c • u = (c : ℚ_[p]) • u := (algebraMap_smul ℚ_[p] c u).symm
  rw [h, hsm]
end PI
