-- Prove2me | solution 1 for P2M_Aggmetrics_DataStream_precision_d__aa400482150b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:32:34.692843+00:00
-- url     : https://prove2.me/submissions/dc817e77-f8d5-4b57-bc4c-ed398c647b7a

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
import Theorems.Thm_Aggmetrics_DataStream_hasDerivAt_ratio_lin

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (R S π : ℝ) (hD : π * R + (1 - π) * (1 - S) ≠ 0) :
    HasDerivAt (fun y => precision R S y)
      (R * (1 - S) / (π * R + (1 - π) * (1 - S)) ^ 2) π := by
  have h := hasDerivAt_ratio_lin R 0 (R - (1 - S)) (1 - S) π (π * R + (1 - π) * (1 - S))
    (by ring) hD
  convert h using 1
  · funext y
    unfold precision
    ring
  · field_simp
    ring
end Aggmetrics.DataStream
