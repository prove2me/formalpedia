-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.scaled_depth_le_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:01:52.328387+00:00
-- url     : https://prove2.me/submissions/0a97a88d-5014-4e42-87ae-1cd71973216f

import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsScales
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsPolynomial
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_scaled_depth_le


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Scales StageBounds Filter Light
open scoped Topology
set_option maxHeartbeats 1200000
set_option maxRecDepth 14000
noncomputable section
namespace ThreeSum.SharedReportingBankResourceBounds
theorem _root_.solution (n : ℕ) : scaledDepth n ≤ envelope n :=
  (scaled_depth_le n).trans (Nat.le_add_right _ _)
end ThreeSum.SharedReportingBankResourceBounds
