-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.resources_of_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:05:55.704012+00:00
-- url     : https://prove2.me/submissions/36673ed9-9f72-45a3-b4e3-f772b8085433

import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsScales
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsPolynomial
import Definitions.Def_WeightedCache3SUM_Alias_0166cf50b135e31f


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Scales StageBounds Filter Light
open scoped Topology
set_option maxHeartbeats 1200000
set_option maxRecDepth 14000
noncomputable section
namespace ThreeSum.SharedReportingBankResourceBounds
theorem _root_.solution {lim : Light.Limits} {n U free NB NC d : ℕ}
    (hB : NB ≤ n) (hC : NC ≤ n) (hok : (need n U).Ok lim free d) :
    LightSharedReportingHost.Resources lim free (half n) (blocks n)
      NB NC (BandScales.bandSize n) d :=
  resources hB hC hok.cells hok.word hok.depth
end ThreeSum.SharedReportingBankResourceBounds
