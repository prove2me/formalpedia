-- Prove2me | solution 1 for TunnellMap.reduceFrame_alpha_le_two_sqrt_div_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:24:54.563286+00:00
-- url     : https://prove2.me/submissions/6ad7c29d-dd5e-492d-9d7d-c79587c5b9b0

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
import Theorems.Thm_TunnellMap_isLagrangeGaussReduced_reduceFrame
import Theorems.Thm_TunnellMap_OrderedGenerator_reduced_alpha_le_two_sqrt_div_three


set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {p : Triple}
namespace TunnellMap
theorem _root_.solution (F : OrthogonalFrame p) :
    (alpha (reduceFrame F) : ℝ) ≤ 2 * Real.sqrt ((dot p p : ℝ) / 3) :=
  reduced_alpha_le_two_sqrt_div_three _ (isLagrangeGaussReduced_reduceFrame F)
end TunnellMap
