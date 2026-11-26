-- Prove2me | solution 1 for Sqrt6KissingBound.upperProfile3_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:14:28.478267+00:00
-- url     : https://prove2.me/submissions/b45601e1-3306-4e7a-9635-6c8601c8aa71

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionThree

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
namespace Sqrt6KissingBound
theorem _root_.solution (t : ℝ) : 0 ≤ upperProfile3 t := Real.sqrt_nonneg _
end Sqrt6KissingBound
