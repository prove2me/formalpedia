-- Prove2me | solution 1 for ThreeSum.PolynomialResources.polyNeed_of_separate_envelopes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:28.626436+00:00
-- url     : https://prove2.me/submissions/ce1f11b5-4dc0-4c51-b639-45b90d2ee3be

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_WeightedCache3SUM_Alias_344aec5f6f2c437a
import Theorems.Thm_Light_polyBound_mono


set_option autoImplicit false
open ThreeSum ThreeSum.PolynomialResources
open StageBounds Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.PolynomialResources
theorem _root_.solution {need : ℕ → ℕ → Light.Need}
    {fw fc fd : ℕ → ℕ} {aw ac ad : ℝ}
    (hw : PowerBound fw aw) (hc : PowerBound fc ac) (hd : PowerBound fd ad)
    (ew ec ed : ℕ)
    (hword : ∀ n U, (need n U).word ≤ fw n*(U+1)^ew)
    (hcells : ∀ n U, (need n U).cells ≤ fc n*(U+1)^ec)
    (hdepth : ∀ n U, (need n U).depth ≤ fd n*(U+1)^ed) : Light.PolyNeed need := by
  obtain ⟨sw,kw,hwb⟩ := pair_polyBound_of_powerBound hw ew
  obtain ⟨sc,kc,hcb⟩ := pair_polyBound_of_powerBound hc ec
  obtain ⟨sd,kd,hdb⟩ := pair_polyBound_of_powerBound hd ed
  refine ⟨sw+sc+sd,kw+kc+kd,fun n U => ⟨?_,?_,?_⟩⟩
  · exact ((hword n U).trans (hwb n U)).trans (Light.polyBound_mono (by omega) (by omega) _)
  · exact ((hcells n U).trans (hcb n U)).trans (Light.polyBound_mono (by omega) (by omega) _)
  · exact ((hdepth n U).trans (hdb n U)).trans (Light.polyBound_mono (by omega) (by omega) _)
end ThreeSum.PolynomialResources
