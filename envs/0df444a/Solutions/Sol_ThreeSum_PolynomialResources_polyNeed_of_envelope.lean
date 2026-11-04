-- Prove2me | solution 1 for ThreeSum.PolynomialResources.polyNeed_of_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:22.73692+00:00
-- url     : https://prove2.me/submissions/006674a3-796c-456d-89e2-8a2129f90b38

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_WeightedCache3SUM_Alias_344aec5f6f2c437a

set_option autoImplicit false
open ThreeSum ThreeSum.PolynomialResources
open StageBounds Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.PolynomialResources
theorem _root_.solution {need : ℕ → ℕ → Light.Need} {f : ℕ → ℕ} {a : ℝ}
    (hf : PowerBound f a) (e : ℕ)
    (hword : ∀ n U, (need n U).word ≤ f n*(U+1)^e)
    (hcells : ∀ n U, (need n U).cells ≤ f n*(U+1)^e)
    (hdepth : ∀ n U, (need n U).depth ≤ f n*(U+1)^e) : Light.PolyNeed need := by
  obtain ⟨s,k,h⟩ := pair_polyBound_of_powerBound hf e
  exact ⟨s,k,fun n U => ⟨(hword n U).trans (h n U),
    (hcells n U).trans (h n U),(hdepth n U).trans (h n U)⟩⟩
end ThreeSum.PolynomialResources
