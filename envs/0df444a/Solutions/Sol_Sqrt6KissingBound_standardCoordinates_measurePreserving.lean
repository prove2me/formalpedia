-- Prove2me | solution 1 for Sqrt6KissingBound.standardCoordinates_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:17:58.414806+00:00
-- url     : https://prove2.me/submissions/114c7ba8-7eea-49ee-9dc7-22767bacfaec

import Mathlib
import Definitions.Def_Sqrt6KissingBound_CoordinateVolume

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution (d : ℕ) :
    MeasurePreserving (standardCoordinates d) := by
  exact
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm _).trans
      (PiLp.volume_preserving_toLp _)
end Sqrt6KissingBound
