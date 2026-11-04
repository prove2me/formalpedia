-- Prove2me | solution 1 for ThreeSum.TernaryHybridResources.powered_fast_poly_need
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:13:07.537488+00:00
-- url     : https://prove2.me/submissions/20999748-b41c-490c-af2b-4a9b121d650d

import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_LightBruteThreeSum
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_TernaryHybridResources
import Theorems.Thm_ThreeSum_TernaryHybridResources_polyBound_substitute_pow

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryHybridResources
open Light StageBounds ArithmeticStageBounds
set_option maxHeartbeats 1700000
set_option maxRecDepth 16000
variable (fastNeed : ℕ → ℕ → Light.Need)
noncomputable section
namespace ThreeSum.TernaryHybridResources
theorem _root_.solution (hf : Light.PolyNeed fastNeed) (κ : ℕ) : Light.PolyNeed (poweredFastNeed fastNeed κ) := by
  obtain ⟨s,e,h⟩ := hf
  refine ⟨s+e,(κ+1)*e,fun n U => ?_⟩
  have hh := h n (n^κ)
  have ht := polyBound_substitute_pow s e κ n U
  exact ⟨hh.1.trans ht,hh.2.1.trans ht,hh.2.2.trans ht⟩
end ThreeSum.TernaryHybridResources
