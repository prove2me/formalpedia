-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalSeedScoreFactory.BuiltO.transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:29:45.463041+00:00
-- url     : https://prove2.me/submissions/7fe258a7-80d0-4764-8045-75a46fdc724c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScore
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalSeedScoreFactory
open Light
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits}
namespace ThreeSum.LightWeightedGlobalSeedScoreFactory
namespace BuiltO
theorem _root_.solution {C : Config} {D : Data C} {μ ν ξ : ℕ → ℤ} {cutoff depth : ℕ}
    (G : AppendGuard C D lim depth μ) (H : BuiltO C D μ ν) (K : Kept ν ξ cutoff)
    (hcut : C.Onew+C.nO≤cutoff) : BuiltO C D μ ξ := by
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
  · intro x hx; rw [K x (by have := G.BC; have := G.CO; omega),H.1.1.1 x hx]
  · intro i hi; rw [K _ (by have := G.BC; have := G.CO; omega),H.1.1.2 i hi]
  · intro i hi; rw [K _ (by have := G.CO; omega),H.1.2 i hi]
  · intro i hi; rw [K _ (by omega),H.2 i hi]
end BuiltO
end ThreeSum.LightWeightedGlobalSeedScoreFactory
