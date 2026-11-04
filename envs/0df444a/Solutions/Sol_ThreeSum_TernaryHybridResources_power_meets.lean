-- Prove2me | solution 1 for ThreeSum.TernaryHybridResources.power_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:26.244967+00:00
-- url     : https://prove2.me/submissions/b8dd27e6-07ab-49d4-b715-9c0e717b32b7

import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_LightBruteThreeSum
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_TernaryHybridResources
import Theorems.Thm_ThreeSum_TernaryHybridResources_scalar_word_of_ok
import Theorems.Thm_ThreeSum_TernaryHybridResources_power_word_of_ok
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightClassFilter_program_meets
import Theorems.Thm_ThreeSum_LightColorIndex_program_meets
import Theorems.Thm_ThreeSum_LightColorParameters_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightNatPower_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryHybridResources
open Light StageBounds ArithmeticStageBounds
set_option maxHeartbeats 1700000
set_option maxRecDepth 16000
variable (fastNeed : ℕ → ℕ → Light.Need)
namespace ThreeSum.TernaryHybridResources
theorem _root_.solution {lim : Limits} {κ cutoff n U free d : ℕ} (μ : ℕ→ℤ)
    (H : (need fastNeed κ cutoff n U).Ok lim free d) :
    Meets lim LightNatPower.program 0 (d+1) [n,κ] μ (LightNatPower.time κ)
      (fun r ν => r=((n^κ : ℕ) : ℤ) ∧ ν=μ) := by
  apply LightNatPower.program_meets μ
  · exact (Int.ofNat_le.mpr (show κ≤n+κ+cutoff+U+(n+1)^(κ+1)+10 by omega)).trans
      (scalar_word_of_ok fastNeed H)
  · intro i hi
    exact power_word_of_ok fastNeed H hi
end ThreeSum.TernaryHybridResources
