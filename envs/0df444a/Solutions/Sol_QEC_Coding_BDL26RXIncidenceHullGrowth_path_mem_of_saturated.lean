-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullGrowth.path_mem_of_saturated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:33:56.841488+00:00
-- url     : https://prove2.me/submissions/be462c7b-9142-4578-ab21-8938017789cb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth

set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXIncidenceHullGrowth
theorem _root_.solution (A : Finset (state S i.val).presentation.Q)
    (closed : IncidenceSaturated S depth i A)
    {q r : (state S i.val).presentation.Q} (hq : q ∈ A)
    (path : SharedZPath (state S i.val).presentation q r) : r ∈ A := by
  induction path with
  | refl => exact hq
  | snoc path z left right ih => exact closed _ ih _ z left right
end QEC.Coding.BDL26RXIncidenceHullGrowth
