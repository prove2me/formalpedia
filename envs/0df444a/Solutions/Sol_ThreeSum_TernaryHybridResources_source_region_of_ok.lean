-- Prove2me | solution 1 for ThreeSum.TernaryHybridResources.source_region_of_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:07:23.555555+00:00
-- url     : https://prove2.me/submissions/a748fa23-30e8-4139-a7cb-3d81f5132a51

import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_LightBruteThreeSum
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_TernaryHybridResources

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryHybridResources
open Light StageBounds ArithmeticStageBounds
set_option maxHeartbeats 1700000
set_option maxRecDepth 16000
variable (fastNeed : ℕ → ℕ → Light.Need)
namespace ThreeSum.TernaryHybridResources
theorem _root_.solution {lim : Limits} {κ cutoff n U src free d : ℕ}
    (H : (need fastNeed κ cutoff n U).Ok lim free d) (hsrc : src+n≤free) :
    src+n≤lim.space ∧ (free : ℤ)≤lim.word := by
  have hf : free≤lim.space := by have hh := H.cells; omega
  exact ⟨hsrc.trans hf,(Int.ofNat_le.mpr hf).trans H.space⟩
end ThreeSum.TernaryHybridResources
