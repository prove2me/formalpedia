-- Prove2me | solution 1 for P2M_Aggmetrics_DataStream_f1_d__b648ab33ec46
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:32:53.323444+00:00
-- url     : https://prove2.me/submissions/7ce42eb4-4a7f-4476-9217-b016e8ce08aa

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
import Theorems.Thm_Aggmetrics_DataStream_hasDerivAt_ratio_lin

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (R S π : ℝ) (hD : π * (1 + R) + (1 - π) * (1 - S) ≠ 0) :
    HasDerivAt (fun y => f1 R S y)
      (2 * R * (1 - S) / (π * (1 + R) + (1 - π) * (1 - S)) ^ 2) π := by
  have h := hasDerivAt_ratio_lin (2 * R) 0 (R + S) (1 - S) π
    (π * (1 + R) + (1 - π) * (1 - S)) (by ring) hD
  convert h using 1
  · funext y
    unfold f1
    ring
  · field_simp
    ring
end Aggmetrics.DataStream
