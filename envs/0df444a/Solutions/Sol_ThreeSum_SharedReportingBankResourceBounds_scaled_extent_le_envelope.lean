-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.scaled_extent_le_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:44:03.702241+00:00
-- url     : https://prove2.me/submissions/ff05f99d-19db-4efd-b9ea-3674122eefb3

import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsScales
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsPolynomial
import Definitions.Def_WeightedCache3SUM_Alias_b95da8361a53d47d


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Scales StageBounds Filter Light
open scoped Topology
set_option maxHeartbeats 1200000
set_option maxRecDepth 14000
noncomputable section
namespace ThreeSum.SharedReportingBankResourceBounds
theorem _root_.solution (n : ℕ) : scaledExtent n ≤ envelope n :=
  (scaled_extent_le n).trans (Nat.le_add_right _ _)
end ThreeSum.SharedReportingBankResourceBounds
