-- Prove2me | solution 1 for ThreeSum.SourceFiniteInputs.prepared_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:17:55.082697+00:00
-- url     : https://prove2.me/submissions/0a693719-7a48-460e-959d-e3fcd7d92a08

import Definitions.Def_Submission_ThreeSum_LightGuardedWanted
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs

set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteInputs
open Light GlobalEncoding LocalCoverBounds LightLocalCoverLayout LightLocalCoverSchedule
namespace ThreeSum.SourceFiniteInputs
theorem _root_.solution {μ : ℕ → ℤ} {values endpoints g U : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : LightBandPreprocessing.Represents μ values endpoints g hg original L hs)
    (hb : ∀ z ∈ original, |z| ≤ (U : ℤ)) :
    ∀ j < L.length, |L.getD j 0| ≤ (U : ℤ) := by
  intro j hj
  rw [List.getD_eq_getElem _ _ hj]
  exact hb _ ((H.2.2.1 _).mp (List.getElem_mem hj))
end ThreeSum.SourceFiniteInputs
