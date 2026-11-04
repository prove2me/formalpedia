-- Prove2me | solution 1 for ThreeSum.TernaryHybridCosts.fastTime_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:30.73405+00:00
-- url     : https://prove2.me/submissions/6d25261a-4662-404f-a3a9-c3a74d8aa577

import Definitions.Def_Submission_ThreeSum_TernaryHybridCore
import Definitions.Def_Submission_ThreeSum_TernaryEndBridge
import Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
import Theorems.Thm_ThreeSumApsp_Dominated_const
import Theorems.Thm_ThreeSumApsp_WordRam_SolvedInTime_mono_exponent
import Definitions.Def_WeightedCache3SUM_Alias_851b6603dbe122fe
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mono_exponent


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryHybridCosts
open Light StageBounds Filter
noncomputable section
namespace ThreeSum.TernaryHybridCosts
theorem _root_.solution {T : ℕ → ℕ} {a : ℝ}
    (hT : PowerBound T a) (ha : 0 ≤ a) (κ : ℕ) :
    PowerBound (fastTime T κ) a := by
  have hp := (PowerBound.const (LightNatPower.time κ)).mono_exponent ha
  have hc := (PowerBound.const 1000).mono_exponent ha
  exact (hT.add_same hp).add_same hc
end ThreeSum.TernaryHybridCosts
