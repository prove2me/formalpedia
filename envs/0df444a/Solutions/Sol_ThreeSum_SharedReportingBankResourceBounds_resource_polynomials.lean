-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.resource_polynomials
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:53:08.239563+00:00
-- url     : https://prove2.me/submissions/8d234651-450f-49c3-826a-844759e8ac2c

import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsScales
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsPolynomial
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_envelope_powerBound
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_scaled_extent_le_envelope
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_scaled_depth_le_envelope
import Theorems.Thm_ThreeSum_PolynomialResources_polyBound_of_powerBound
import Definitions.Def_WeightedCache3SUM_Alias_2af3298e1979157a


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Scales StageBounds Filter Light
open scoped Topology
set_option maxHeartbeats 1200000
set_option maxRecDepth 14000
noncomputable section
namespace ThreeSum.SharedReportingBankResourceBounds
theorem _root_.solution : ∃ s k : ℕ, ∀ n : ℕ,
    scaledWord n ≤ Light.polyBound s k [n] ∧
    scaledExtent n ≤ Light.polyBound s k [n] ∧
    scaledDepth n ≤ Light.polyBound s k [n] := by
  obtain ⟨s,k,h⟩ := PolynomialResources.polyBound_of_powerBound envelope_powerBound
  exact ⟨s,k,fun n => ⟨(scaled_word_le n).trans (h n),
    (scaled_extent_le_envelope n).trans (h n),
    (scaled_depth_le_envelope n).trans (h n)⟩⟩
end ThreeSum.SharedReportingBankResourceBounds
