-- Prove2me | solution 1 for ReciprocityTheory.PTheta.thetaSummable_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:37:04.512016+00:00
-- url     : https://prove2.me/submissions/96485d4a-172d-4e20-8f02-989da83bdfb2

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
import Theorems.Thm_ReciprocityTheory_PTheta_thetaMTest_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta
open sphereQuadraticPositivity
namespace ReciprocityTheory.PTheta
theorem _root_.solution : ThetaSummableStatement := by
  intro ι _ a b z τ hτ
  obtain ⟨u, hu, hb⟩ := thetaMTest_holds ι a {(z, Matrix.of.symm τ)} isCompact_singleton
    (by rintro p rfl; simpa using hτ)
  refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => ?_) hu
  simpa using hb b (z, Matrix.of.symm τ) rfl l
end ReciprocityTheory.PTheta
