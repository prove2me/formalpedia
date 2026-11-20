-- Prove2me | solution 1 for P2M_Aggmetrics_DataStream_natAbs_sub_of_lt__f4533c285d97
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:30:52.383315+00:00
-- url     : https://prove2.me/submissions/422a607e-9a5c-4c8a-aa8e-cb1e2a3f014f

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr

set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {i t : ℕ} (h : i < t) : Int.natAbs ((t : ℤ) - (i : ℤ)) = t - i := by
  have e : ((t : ℤ) - (i : ℤ)) = ((t - i : ℕ) : ℤ) := by omega
  rw [e]
  simp
end Aggmetrics.DataStream
